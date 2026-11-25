import Shellsort.ConsecutiveMenus
import Shellsort.ConsecutiveBlockBounds
import Shellsort.HarvestLinearLowMenu
import Shellsort.HarvestCutSpectrum
import Shellsort.HarvestCutTotals

/-! Counting all modes as small denominators proves a quadratic-in-center
footrule fee with no large-sieve premise. -/
noncomputable section
namespace Shellsort.ConsecutiveMenus
open Actual214 Finset RoughGapScaleAssembly RoughGapEndpoint RoughGapDenominatorAverage

/-- Sum over a general finite gap menu. Divisors common to both retained gaps
must be absent from the selected gaps; no density assumption is needed here. -/
theorem square_sum {n g₁ g₂ B : ℕ} (p : RankPlacement n)
    (hg : 0 < g₂) (order : g₂ ≤ g₁) (G : Finset ℕ)
    (bounds : ∀ h ∈ G, 0 < h ∧ h ≤ B)
    (breaks : ∀ h ∈ G, ∀ d, d ∣ h → 1 < d → ¬ d ∣ g₁ ∨ ¬ d ∣ g₂) :
    let z := gapSort (gapSort p g₁) g₂
    (∑ h ∈ G, (squareDisplacement (gapSort z h) : ℝ)) ≤
      ((B:ℝ)*g₁*B) * footrule p := by
  intro z
  let E (t h a : ℕ) := energy 0 (fun i : Fin n => (slotError z (t+1) i : ℂ)) (a,h)
  have all_modes (h : ℕ) (hh : h ∈ G) : lowGrid h B = (range h).filter (0 < ·) := by
    ext a
    have denom := (Nat.div_le_self h (h.gcd a)).trans (bounds h hh).2
    simp [lowGrid,denom]
  calc
    _ ≤ ∑ h ∈ G, ∑ t ∈ range n, ∑ a ∈ lowGrid h B, E t h a := by
      apply sum_le_sum
      intro h hh
      rw [all_modes h hh]
      exact HarvestCutSpectrum.square_le_physical_spectrum z (bounds h hh).1
    _ = ∑ t ∈ range n, ∑ h ∈ G, ∑ a ∈ lowGrid h B, E t h a := sum_comm
    _ ≤ ∑ t ∈ range n, ((B:ℝ)*g₁*B)*(∑ i, |(slotError p (t+1) i : ℝ)|) :=
      sum_le_sum fun t ht => linear_low_menu_of_divisors p _ (mem_range.mp ht) hg order G
        breaks (fun h hh => (bounds h hh).2)
    _ = _ := by rw [← mul_sum, HarvestCutTotals.total_cut_mass]

/-- For every seed center up to 49,932 the sharp manuscript coefficient of
cF holds on its own, for every array length and every fixed entrance state. -/
theorem small_center_contraction {n : ℕ} (p : RankPlacement n) (j : ℕ)
    (small : gap j ≤ 49932) :
    (∑ h ∈ menu j, (squareDisplacement
      (gapSort (gapSort (gapSort p (gap (j+2))) (gap (j+1))) h) : ℝ)) /
        (menu j).card ≤ 2^24 * (gap j:ℝ) * footrule p := by
  let c := gap j
  let g₁ := gap (j+2)
  let g₂ := gap (j+1)
  have density : 3 * (c:ℝ) ≤ 7 * ((menu j).card:ℝ) := by exact_mod_cast menu_density j
  have positive := gap_pos j
  have card_pos : 0 < ((menu j).card:ℝ) := by
    have := menu_density j
    exact_mod_cast (show 0 < (menu j).card by omega)
  have gmax : (g₁:ℝ) ≤ 16*c := by
    exact_mod_cast (HarvestStageArithmetic.four_growth j 2)
  have cmax : (c:ℝ) ≤ 49932 := by exact_mod_cast small
  have cp : 0 ≤ (c:ℝ) := Nat.cast_nonneg _
  have breaks (h : ℕ) (hh : h ∈ menu j) (d : ℕ) (dvd : d ∣ h) (big : 1 < d) :
      ¬ d ∣ g₁ ∨ ¬ d ∣ g₂ := by
    by_contra! both
    have dh := Nat.dvd_gcd (Nat.dvd_gcd both.2 both.1) dvd
    change d ∣ (modulus j).gcd h at dh
    rw [show (modulus j).gcd h = 1 from (mem_filter.mp hh).2] at dh
    exact (Nat.not_dvd_of_pos_of_lt (by decide) big) dh
  have sum_bound := square_sum p (gap_pos (j+1))
    (show g₂ ≤ g₁ from HarvestStageArithmetic.gap_strict.monotone (by omega : j+1 ≤ j+2))
    (menu j) (B:=3*c) (fun h hh => by
      have hi := (mem_Ico.mp (mem_filter.mp hh).1).2
      dsimp [upper] at hi
      exact ⟨(menu_order hh).1,by dsimp [c]; omega⟩) breaks
  apply (div_le_iff₀ card_pos).mpr
  apply sum_bound.trans
  push_cast
  have F : 0 ≤ footrule p := by unfold footrule transport; positivity
  have coeff : (3*(c:ℝ))*g₁*(3*c) ≤ (2^24*c)*((menu j).card:ℝ) := calc
    _ ≤ (3*(c:ℝ))*(16*c)*(3*c) := by gcongr
    _ = (336*c)*c*((3*c)/7) := by ring
    _ ≤ (2^24*c)*((menu j).card:ℝ) := by
      have factor : 336*(c:ℝ) ≤ 2^24 := by linarith
      have mass : (3*(c:ℝ))/7 ≤ ((menu j).card:ℝ) := by linarith
      gcongr
  convert mul_le_mul_of_nonneg_right coeff F using 1
  ring

/-- At a verified center, retaining a fraction η of the menu costs at most
a factor 1/η in the mean square bound, for each entrance permutation. -/
theorem small_center_submenu {n : ℕ} (p : RankPlacement n) (j : ℕ)
    (small : gap j ≤ 49932) (G : Finset ℕ) (sub : G ⊆ menu j)
    (η : ℝ) (positive : 0 < η) (mass : η * (menu j).card ≤ G.card) :
    (∑ h ∈ G, (squareDisplacement
      (gapSort (gapSort (gapSort p (gap (j+2))) (gap (j+1))) h) : ℝ)) /
        G.card ≤ (2^24 * (gap j:ℝ) * footrule p) / η := by
  let E (h : ℕ) : ℝ := squareDisplacement
    (gapSort (gapSort (gapSort p (gap (j+2))) (gap (j+1))) h)
  let bound : ℝ := 2^24 * (gap j:ℝ) * footrule p
  have cost : 0 ≤ bound := by unfold bound footrule transport; positivity
  have menu_pos : 0 < ((menu j).card:ℝ) := by
    have := menu_density j
    have := gap_pos j
    exact_mod_cast (show 0 < (menu j).card by omega)
  have retained := (mul_pos positive menu_pos).trans_le mass
  have smallMean : (∑ h ∈ menu j, E h) / (menu j).card ≤ bound :=
    small_center_contraction p j small
  have subsetSum : (∑ h ∈ G, E h) ≤ ∑ h ∈ menu j, E h :=
    sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by unfold E squareDisplacement; positivity)
  change (∑ h ∈ G, E h) / G.card ≤ bound / η
  rw [div_le_div_iff₀ retained positive]
  calc
    _ ≤ (bound * (menu j).card) * η :=
      mul_le_mul_of_nonneg_right (subsetSum.trans ((div_le_iff₀ menu_pos).1 smallMean)) positive.le
    _ = bound * (η * (menu j).card) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left mass cost

/-- Starting from the indicated entrance budget, the next scale is reached
under a fresh uniform menu draw at every center in the proved range. -/
theorem random_small_center {n : ℕ} (hn : 0 < n) (j : ℕ) (small : gap j ≤ 49932)
    {ι : Type*} [Fintype ι] (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (total : ∑ i, weight i = 1) (state : ι → RankPlacement n)
    (prior : (∑ i, weight i * RoughGapSelection.energy (state i)) ≤
      ((19*2^24) * ConsecutiveBlockBounds.scale (j+3))^2) :
    (∑ i, weight i * ((∑ h ∈ menu j,
      RoughGapSelection.energy (HarvestScaleNumbers.block j h (state i))) /
        (menu j).card)) ≤ ((19*2^24)*ConsecutiveBlockBounds.scale j)^2 := by
  apply ConsecutiveBlockBounds.random_block_propagate hn j weight hw total state prior
  intro p
  have point := div_le_div_of_nonneg_right (small_center_contraction p j small)
    (show 0 ≤ (n:ℝ) by positivity)
  unfold RoughGapSelection.energy RoughGapSelection.mass
  rw [← sum_div, div_right_comm]
  have Q : 0 ≤ (squareDisplacement p : ℝ) := by unfold squareDisplacement; positivity
  change _ ≤ (squareDisplacement p : ℝ) / n / 200 + _
  apply point.trans
  rw [mul_div_assoc]
  exact le_add_of_nonneg_left (by positivity)

end Shellsort.ConsecutiveMenus
