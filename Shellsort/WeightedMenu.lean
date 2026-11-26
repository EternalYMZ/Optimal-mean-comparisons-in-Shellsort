import Shellsort.ConsecutiveMenuEnergy

/-! Bounded-atom transfer and its unconditional application to the checked
consecutive three-pass blocks. From the built P04 proof project run
  lake env lean /path/to/WeightedMenu.lean
-/

noncomputable section
namespace Shellsort.WeightedMenu
open Finset Actual214 ConsecutiveMenus RoughGapScaleAssembly

/-- An atom bound times the cardinality converts a uniform energy estimate
on a finite set into a weighted estimate on its individual outcomes. -/
private theorem compare_means (G : Finset ℕ) (w e : ℕ → ℝ) {T : ℝ}
    (cap : ∀ h ∈ G, w h ≤ T / G.card) (pos : ∀ h ∈ G, 0 ≤ e h) :
    (∑ h ∈ G, w h * e h) ≤ T * ((∑ h ∈ G, e h) / G.card) := by
  calc
    _ ≤ ∑ h ∈ G, (T / G.card) * e h :=
      sum_le_sum fun h hh => mul_le_mul_of_nonneg_right (cap h hh) (pos h hh)
    _ = _ := by rw [← mul_sum]; ring

/-- The normalized weights force at least c/L menu entries. The coefficient
loss in a uniform estimate is at most L H when |G| ≤ H c. -/
theorem bounded_atom_reduction (G : Finset ℕ) (w e : ℕ → ℝ) {c L H D : ℝ}
    (hc : 0 < c) (hL : 0 < L) (total : ∑ h ∈ G, w h = 1)
    (cap : ∀ h ∈ G, w h ≤ L / c) (card : (G.card : ℝ) ≤ H * c)
    (pos : ∀ h ∈ G, 0 ≤ e h) (uniform : (∑ h ∈ G, e h) / G.card ≤ D) :
    c / L ≤ (G.card : ℝ) ∧ (∑ h ∈ G, w h * e h) ≤ (L * H) * D := by
  have mass : 1 ≤ (G.card : ℝ) * (L / c) := by
    calc
      1 = ∑ h ∈ G, w h := total.symm
      _ ≤ ∑ _h ∈ G, L / c := sum_le_sum cap
      _ = _ := by simp
  have lower : c / L ≤ (G.card : ℝ) := by
    rw [← mul_div_assoc] at mass
    exact (div_le_iff₀ hL).2 (by simpa using (le_div_iff₀ hc).mp mass)
  have gpos := (div_pos hc hL).trans_le lower
  have adjusted (h : ℕ) (hh : h ∈ G) : w h ≤ (L * H) / G.card := by
    apply (cap h hh).trans
    apply (div_le_div_iff₀ hc gpos).2
    calc
      _ ≤ L * (H * c) := mul_le_mul_of_nonneg_left card hL.le
      _ = _ := by ring
  have hH : 0 < H := pos_of_mul_pos_left (gpos.trans_le card) hc.le
  exact ⟨lower, (compare_means G w e adjusted pos).trans
    (mul_le_mul_of_nonneg_left uniform (mul_pos hL hH).le)⟩

/-- For the concrete executed checkpoint, bounded-atom sampling multiplies
the verified small-center energy bound by at most T. An entrance state is
arbitrary and the upper range restriction is solely on the center. -/
theorem small_center_weighted {n : ℕ} (p : RankPlacement n) (j : ℕ)
    (small : gap j ≤ 49932) (w : ℕ → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (cap : ∀ h ∈ menu j, w h ≤ T / (menu j).card) :
    (∑ h ∈ menu j, w h * (squareDisplacement
      (gapSort (gapSort (gapSort p (gap (j+2))) (gap (j+1))) h) : ℝ))
      ≤ T * (2^24 * (gap j : ℝ) * footrule p) := by
  apply (compare_means (menu j) w _ cap _).trans
    (mul_le_mul_of_nonneg_left (small_center_contraction p j small) hT)
  intro h _
  unfold squareDisplacement
  positivity

#print axioms bounded_atom_reduction
#print axioms small_center_weighted

end Shellsort.WeightedMenu
