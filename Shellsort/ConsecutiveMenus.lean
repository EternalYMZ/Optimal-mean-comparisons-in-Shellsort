import Shellsort.HarvestStageArithmetic
import Mathlib.Data.Nat.Totient

/-! Menus for the consecutive three-pass schedule. Complete residue periods
give the density for large centers; the first ten seeds use their actual gcd. -/
namespace Shellsort.ConsecutiveMenus
open Actual214 Finset

def lower (c : ℕ) := (c + 1) / 2
def upper (c : ℕ) := 107 * c / 50 + 1
def modulus (j : ℕ) := (gap (j + 1)).gcd (gap (j + 2))
def menu (j : ℕ) :=
  (Ico (lower (gap j)) (upper (gap j))).filter ((modulus j).Coprime ·)

private theorem periods (a d q : ℕ) :
    ((Ico a (a + d*q)).filter (d.Coprime ·)).card = q*d.totient := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, ← Ico_union_Ico_eq_Ico (show a ≤ a+d*q by omega)
      (show a+d*q ≤ a+d*q+d by omega), filter_union, card_union_of_disjoint]
    · rw [ih, Nat.filter_coprime_Ico_eq_totient, Nat.succ_mul]
    · apply Finset.disjoint_left.mpr
      intro x hx hy
      have := (mem_Ico.mp (mem_filter.mp hx).1).2
      have := (mem_Ico.mp (mem_filter.mp hy).1).1
      omega

private theorem interval_lower (a b d : ℕ) :
    ((b-a)/d)*d.totient ≤ ((Ico a b).filter (d.Coprime ·)).card := by
  by_cases hab : a ≤ b
  · rw [← periods a]
    apply card_le_card
    apply filter_subset_filter
    apply Ico_subset_Ico_right
    have := Nat.mul_div_le (b-a) d
    omega
  · simp [Nat.sub_eq_zero_of_le (by omega : b ≤ a)]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 3000000 in
private theorem phi_budget (d : Fin 95) : 4*d.val ≤ 15*d.val.totient := by
  exact (by decide : ∀ x : Fin 95, 4*x.val ≤ 15*x.val.totient) d

private theorem large_center {j : ℕ} (hc : 3000 ≤ gap j) :
    3 * gap j ≤ 7 * (menu j).card := by
  let c := gap j
  let d := modulus j
  let width := upper c - lower c
  let q := width / d
  have dpos : 0 < d := Nat.gcd_pos_of_pos_left _ (gap_pos _)
  have dmax : d ≤ 94 := adjacent_gap_gcd_le (j+1)
  have tot := phi_budget ⟨d,by omega⟩
  change 4*d ≤ 15*d.totient at tot
  have avail : q*d.totient ≤ (menu j).card := interval_lower _ _ _
  have h := Nat.mul_le_mul_left q tot
  have many : 4*(q*d) ≤ 15*(menu j).card := by
    calc
      4*(q*d) = q*(4*d) := by ring
      _ ≤ q*(15*d.totient) := h
      _ = 15*(q*d.totient) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ avail
  have rem : width < q*d + 94 := by
    have := Nat.mod_add_div width d
    have := Nat.mod_lt width dpos
    change width < (width/d)*d + 94
    rw [Nat.mul_comm (width/d) d]
    omega
  have widthBound : 82*c ≤ 50*width + 50 := by dsimp [width,upper,lower]; omega
  change 3000 ≤ c at hc
  change 3*c ≤ _
  omega

/-- Uniform density for the actual menu at every seed, including c = 1. -/
theorem menu_density (j : ℕ) : 3 * gap j ≤ 7 * (menu j).card := by
  by_cases large : 10 ≤ j
  · apply large_center
    exact (by decide : 3000 ≤ gap 10).trans (HarvestStageArithmetic.gap_strict.monotone large)
  · have small : j ≤ 9 := by omega
    by_cases first : j = 0
    · subst j; decide
    by_cases fourth : j = 3
    · subst j; decide
    have mod_one : modulus j = 1 := by interval_cases j <;> first | contradiction | decide
    rw [menu, mod_one]
    rw [filter_true_of_mem (fun x _ => Nat.coprime_one_left x), Nat.card_Ico]
    dsimp [upper, lower]
    omega

theorem menu_order {j h : ℕ} (hh : h ∈ menu j) :
    0 < h ∧ h < gap (j+1) ∧ (∀ i, j = i+1 → gap i < h) := by
  obtain ⟨lo,hi⟩ := mem_Ico.mp (mem_filter.mp hh).1
  dsimp [lower,upper] at lo hi
  have post := scaled_next_bounds (gap j)
  change _ ≤ 50 * gap (j+1) ∧ _ at post
  have pos := gap_pos j
  refine ⟨by omega, by omega, ?_⟩
  intro i eq
  subst j
  have pre := (scaled_next_bounds (gap i)).1
  change _ ≤ 50 * gap (i+1) at pre
  omega

/-- The success probability of one uniform interval proposal exceeds 1/5. -/
theorem proposal_acceptance (j : ℕ) :
    (Ico (lower (gap j)) (upper (gap j))).card < 5*(menu j).card := by
  have h := menu_density j
  have p := gap_pos j
  rw [Nat.card_Ico]
  unfold upper lower
  omega

end Shellsort.ConsecutiveMenus
