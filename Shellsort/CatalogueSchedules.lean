import Shellsort.PredeterminedOptimum
import Shellsort.HarvestCutTotals

/-! Assembly for a finite list of block scales, presented by indexed
endpoints. The contraction and cost inequalities are explicit premises.
From the built P04 proof project run lake env lean /path/to/CatalogueSchedules.lean.
-/

noncomputable section
namespace Shellsort.CatalogueSchedules
open Finset HarvestBlockIteration PredeterminedOptimum

/-- From one local quadratic contraction recover the next scale budget. -/
private theorem propagate {x y a b R K s t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hK : 0 < K)
    (ht : 0 < t) (ratio : s ≤ R * t)
    (calibration : a * (K * R)^2 + b * (K * R) ≤ K^2)
    (budget : Real.sqrt x ≤ K * s) (hx : 0 ≤ x)
    (step : y ≤ a * x + b * t * Real.sqrt x) :
    Real.sqrt y ≤ K * t := by
  have endBound := budget.trans (mul_le_mul_of_nonneg_left ratio hK.le)
  have sqBound : x ≤ (K * (R * t))^2 := by
    rw [← Real.sq_sqrt hx]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg x) endBound 2
  apply Real.sqrt_le_iff.mpr
  refine ⟨(mul_pos hK ht).le, step.trans ?_⟩
  calc
    _ ≤ a * (K * (R * t))^2 + b * t * (K * (R * t)) :=
      add_le_add (mul_le_mul_of_nonneg_left sqBound ha)
        (mul_le_mul_of_nonneg_left endBound (mul_nonneg hb ht.le))
    _ = (a * (K * R)^2 + b * (K * R)) * t^2 := by ring
    _ ≤ K^2 * t^2 := mul_le_mul_of_nonneg_right calibration (sq_nonneg t)
    _ = _ := by ring

/-- For m arbitrary blocks, X denotes the expected square displacement per
key. The cost premise allows displacement charges at both ends of a block.
The conclusion is uniform in all m+1 entrance/exit distributions. -/
theorem assemble (m n : ℕ) (scale X cost : ℕ → ℝ)
    {a b R K u v w : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hK : 0 < K) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (calibration : a * (K * R)^2 + b * (K * R) ≤ K^2)
    (positive : ∀ i ≤ m, 0 < scale i) (energy : ∀ i < m, 0 ≤ X i)
    (ratio : ∀ i < m, scale i ≤ R * scale (i+1))
    (initial : Real.sqrt (X 0) ≤ K * scale 0)
    (contract : ∀ i < m, X (i+1) ≤ a * X i + b * scale (i+1) * Real.sqrt (X i))
    (charge : ∀ i < m, cost i ≤ n * (u +
      (v * Real.sqrt (X i) + w * Real.sqrt (X (i+1))) / scale (i+1))) :
    (∀ i ≤ m, Real.sqrt (X i) ≤ K * scale i) ∧
      ∑ i ∈ range m, cost i ≤ m * (n * (u + v * K * R + w * K)) := by
  have invariant (i : ℕ) (bound : i ≤ m) : Real.sqrt (X i) ≤ K * scale i := by
    induction i with
    | zero => exact initial
    | succ i ih =>
      have hi : i < m := bound
      exact propagate ha hb hK (positive _ bound)
        (ratio i hi) calibration (ih hi.le) (energy i hi) (contract i hi)
  refine ⟨invariant, ?_⟩
  calc
    _ ≤ ∑ _i ∈ range m, (n : ℝ) * (u + v * K * R + w * K) := by
      apply sum_le_sum
      intro i mem
      have hi := mem_range.mp mem
      have start := (invariant i hi.le).trans (mul_le_mul_of_nonneg_left (ratio i hi) hK.le)
      have stop := invariant (i+1) hi
      apply (charge i hi).trans
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
      rw [add_assoc]
      apply add_le_add (le_refl u)
      apply (div_le_iff₀ (positive (i+1) hi)).2
      calc
        _ ≤ v * (K * (R * scale (i+1))) + w * (K * scale (i+1)) :=
          add_le_add (mul_le_mul_of_nonneg_left start hv) (mul_le_mul_of_nonneg_left stop hw)
        _ = _ := by ring
    _ = _ := by simp

/-- For each center 8^j (j=1,...,k) select any third gap in [8^j,2*8^j].
Blocks are executed in descending order, followed by exactly one final gap 1. -/
abbrev Choices := (j : ℕ) → {h : ℕ // 8^j ≤ h ∧ h ≤ 2 * 8^j}

private def firstGap (j : ℕ) : {h : ℕ // 0 < h} := ⟨4 * 8^j + 2, by positivity⟩
private def secondGap (j : ℕ) : {h : ℕ // 0 < h} := ⟨4 * 8^j, by positivity⟩
private def thirdGap (pick : Choices) (j : ℕ) : {h : ℕ // 0 < h} :=
  ⟨(pick j).val, (by positivity : 0 < 8^j).trans_le (pick j).property.1⟩

theorem anchor_admissible (c h : ℕ) :
    h.Coprime ((4*c+2).gcd (4*c)) ↔ Odd h := by
  rw [Nat.add_comm (4*c) 2, Nat.gcd_add_self_left,
      Nat.gcd_eq_left (show 2 ∣ 4*c from ⟨2*c, by omega⟩), Nat.coprime_two_right]

/-- A local spectral estimate on the good component suffices. The other
component is any normalized law; its estimate follows from deterministic
square-displacement monotonicity at each of the three actual checkpoints. -/
theorem mixture_energy {n : ℕ} (p : RankPlacement n) (g₁ g₂ : ℕ)
    (good bad : Finset ℕ) (ν μ : ℕ → ℝ) {δ ε fee : ℝ}
    (mass : ∑ h ∈ bad, μ h = 1) (weights : ∀ h ∈ bad, 0 ≤ μ h)
    (hp : 0 ≤ δ) (hq : δ ≤ 1) (eps : 0 ≤ ε) (fee_pos : 0 ≤ fee) :
    let Q : ℝ := RoughGapScaleAssembly.squareDisplacement p
    let E : ℕ → ℝ := fun h =>
      RoughGapScaleAssembly.squareDisplacement (gapSort (gapSort (gapSort p g₁) g₂) h)
    (∑ h ∈ good, ν h * E h) ≤ ε * Q + fee →
      (1 - δ) * (∑ h ∈ good, ν h * E h) + δ * (∑ h ∈ bad, μ h * E h)
        ≤ (ε + δ) * Q + fee := by
  intro Q E spectral
  have Qpos : 0 ≤ Q := by dsimp [Q, RoughGapScaleAssembly.squareDisplacement]; positivity
  have each (h : ℕ) : E h ≤ Q := by
    dsimp [E, Q]
    exact_mod_cast (HarvestCutTotals.square_le _ h).trans
      ((HarvestCutTotals.square_le _ g₂).trans (HarvestCutTotals.square_le p g₁))
  have bad_bound : (∑ h ∈ bad, μ h * E h) ≤ Q := by
    calc
      _ ≤ ∑ h ∈ bad, μ h * Q :=
        sum_le_sum fun h hh => mul_le_mul_of_nonneg_left (each h) (weights h hh)
      _ = Q := by rw [← sum_mul, mass, one_mul]
  calc
    _ ≤ (1 - δ) * (ε * Q + fee) + δ * Q :=
      add_le_add (mul_le_mul_of_nonneg_left spectral (sub_nonneg.mpr hq))
        (mul_le_mul_of_nonneg_left bad_bound hp)
    _ ≤ (ε + δ) * Q + fee := by
      nlinarith only [mul_nonneg hp (add_nonneg (mul_nonneg eps Qpos) fee_pos)]

def eightTable (pick : Choices) : ℕ → PositiveWord
  | 0 => [⟨1, by decide⟩]
  | k+1 => firstGap (k+1) :: secondGap (k+1) :: thirdGap pick (k+1) :: eightTable pick k

private theorem prepend {g : {j : ℕ // 0 < j}} {w : PositiveWord} {n : ℕ}
    (tail : Legal g.val w) (size : g.val < n) : Legal n (g :: w) := by
  obtain ⟨order, bound, last⟩ := tail
  refine ⟨List.pairwise_cons.mpr ⟨?_, order⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact bound z hz
  · intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact size
    · exact (bound z hz).trans size
  · cases w with
    | nil => simp at last
    | cons x xs => simpa only [List.map_cons, List.getLast?_cons_cons] using last

/-- The permitted choices include both odd and even third gaps. -/
theorem eightTable_legal (pick : Choices) (k n : ℕ) (hn : 1 < n)
    (fits : 0 < k → 4 * 8^k + 2 < n) : Legal n (eightTable pick k) := by
  induction k generalizing n with
  | zero =>
    refine ⟨List.pairwise_singleton _ _, ?_, rfl⟩
    intro z hz
    have eq : z = (⟨1, by decide⟩ : {j : ℕ // 0 < j}) := List.mem_singleton.mp hz
    exact eq ▸ hn
  | succ k ih =>
    have power : 0 < 8^k := by positivity
    have lo := (pick (k+1)).property.1
    have hi := (pick (k+1)).property.2
    have expand : 8^(k+1) = 8^k * 8 := pow_succ _ _
    have next := fits (Nat.succ_pos _)
    apply prepend (g := firstGap (k+1)) _ next
    apply prepend (g := secondGap (k+1))
    · apply prepend (g := thirdGap pick (k+1))
      · apply ih
        · change 1 < (pick (k+1)).val; omega
        · intro _; change 4 * 8^k + 2 < (pick (k+1)).val; omega
      · change (pick (k+1)).val < 4 * 8^(k+1); omega
    · change 4 * 8^(k+1) < 4 * 8^(k+1) + 2; omega

theorem eightTable_length (pick : Choices) (k : ℕ) : (eightTable pick k).length = 3*k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [eightTable, List.length_cons, ih]; omega

/-- At ratio eight, any bad mass strictly below 1/64 leaves room for a
positive good-menu contraction coefficient. The scale constant may be chosen
after the resulting linear fee b is known. -/
theorem eight_calibration {θ : ℝ} (room : θ < 1/64) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ b : ℝ, ∃ K : ℝ, 0 < K ∧
      (θ + ε) * (K * 8)^2 + b * (K * 8) ≤ K^2 := by
  let ε : ℝ := (1/64 - θ) / 2
  have ep : 0 < ε := by dsimp [ε]; linarith
  have dp : 0 < 1 - 64*(θ + ε) := by dsimp [ε]; linarith
  refine ⟨ε, ep, fun b => ?_⟩
  let K := max 1 (8*b / (1 - 64*(θ + ε)))
  have kp : 0 < K := zero_lt_one.trans_le (le_max_left ..)
  have fee : 8*b ≤ K*(1 - 64*(θ + ε)) := (div_le_iff₀ dp).mp (le_max_right ..)
  refine ⟨K, kp, ?_⟩
  nlinarith only [mul_le_mul_of_nonneg_left fee kp.le]

#print axioms assemble
#print axioms eightTable_legal
#print axioms eightTable_length
#print axioms eight_calibration
#print axioms anchor_admissible
#print axioms mixture_energy

end Shellsort.CatalogueSchedules
