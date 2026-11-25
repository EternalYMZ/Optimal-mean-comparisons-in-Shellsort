import Shellsort.HarvestOperationalAudit
import Shellsort.ConsecutiveMenus

/-! The revised three-pass argument charges the last pass at both actual
endpoints. The scale lemmas below propagate a supplied quadratic contraction. -/
noncomputable section
namespace Shellsort.ConsecutiveBlockBounds
open Actual214 HarvestOperationalAudit

/-- Key comparisons of the actual linear insertion pass with positive gap. -/
theorem pass_endpoints {n : ℕ} (p : RankPlacement n) (h : {k : ℕ // 0 < k}) :
    (gapComparisonCost p h.val h.property : ℝ) ≤
      n + (footrule p + footrule (gapSort p h.val)) / h.val := by
  have shifts : (gapInsertionCost p h.val h.property : ℝ) ≤ chainFootrule p h.val := by
    rw [gapInsertionCost_eq_gapInversions]
    exact gapInversions_le_chainFootrule p h.val h.property
  have cmp : (gapComparisonCost p h.val h.property : ℝ) ≤
      (gapInsertionCost p h.val h.property : ℝ) + n := by
    exact_mod_cast gapComparisonCost_upper p h.val h.property
  have geom : chainFootrule p h.val ≤ (footrule p + footrule (gapSort p h.val)) / h.val := by
    apply (le_div_iff₀ (by exact_mod_cast h.property : 0 < (h.val : ℝ))).mpr
    rw [mul_comm, ← gapSort_transport_eq_mul_chainFootrule _ _ h.property]
    exact transport_le_footrules _ _
  linarith

/-- A pathwise bound for every three positive gaps and every input. The exit
footrule is evaluated after this same execution, even when the last gap varies. -/
theorem three_pass_endpoints {n : ℕ} (p : RankPlacement n)
    (g₁ g₂ h : {k : ℕ // 0 < k}) :
    ((runWord (slots p) [g₁,g₂,h]).2 : ℝ) ≤ 3*n +
      2 * footrule p / g₁.val + 2 * footrule p / g₂.val +
      (footrule p + footrule (sortWord p [g₁.val,g₂.val,h.val])) / h.val := by
  let p₁ := gapSort p g₁.val
  let p₂ := gapSort p₁ g₂.val
  have a : footrule p₁ ≤ footrule p := gapSort_footrule_le _ _
  have b : footrule p₂ ≤ footrule p₁ := gapSort_footrule_le _ _
  have first := (pass_endpoints p g₁).trans (show _ ≤ (n:ℝ) + 2*footrule p/g₁.val by
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_right _ (by positivity)
    change footrule p + footrule p₁ ≤ _
    linarith)
  have second := (pass_endpoints p₁ g₂).trans (show _ ≤ (n:ℝ) + 2*footrule p/g₂.val by
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_right _ (by positivity)
    change footrule p₁ + footrule p₂ ≤ _
    linarith)
  have third := (pass_endpoints p₂ h).trans (show _ ≤ (n:ℝ) +
      (footrule p + footrule (gapSort p₂ h.val))/h.val by
    gcongr
    exact b.trans a)
  rw [runWord_slots]
  simp only [ordinaryWordComparisons, sortWord, add_zero, Nat.cast_add]
  change (gapComparisonCost p _ _ : ℝ) +
    ((gapComparisonCost p₁ _ _ : ℝ) + (gapComparisonCost p₂ _ _ : ℝ)) ≤ _
  change _ ≤ 3*(n:ℝ) + _ + _ + (footrule p + footrule (gapSort p₂ h.val))/_
  linarith only [first,second,third]

def scale (j : ℕ) : ℝ := gap j + 94/57

theorem scale_step (j : ℕ) : scale (j+1) ≤ (107/50) * scale j := by
  have h : (50:ℝ)*gap (j+1) ≤ 107*(gap j:ℝ)+94 := by
    exact_mod_cast (scaled_next_bounds (gap j)).2
  dsimp [scale]
  linarith

theorem scale_three (j : ℕ) : scale (j+3) ≤ (107/50)^3 * scale j := by
  linarith only [scale_step j, scale_step (j+1), scale_step (j+2)]

/-- One transition at any scale under the numeric recurrence in Section 6. -/
theorem propagate (j : ℕ) {X Y : ℝ}
    (prior : X ≤ ((19*2^24) * scale (j+3))^2)
    (step : Y ≤ X/200 + 2^24*(gap j:ℝ)*Real.sqrt X) :
    Y ≤ ((19*2^24) * scale j)^2 := by
  let R : ℝ := (107/50)^3
  let K : ℝ := 19*2^24
  have pos : 0 ≤ scale j := by unfold scale; positivity
  have inpos : 0 ≤ scale (j+3) := by unfold scale; positivity
  have growth : K * scale (j+3) ≤ K*(R*scale j) := by
    exact mul_le_mul_of_nonneg_left (scale_three j) (by dsimp [K]; norm_num)
  have xmax : X ≤ (K*(R*scale j))^2 :=
    prior.trans (pow_le_pow_left₀ (mul_nonneg (by dsimp [K]; norm_num) inpos) growth 2)
  have rt := (Real.sqrt_le_sqrt xmax).trans_eq
    (Real.sqrt_sq (mul_nonneg (by dsimp [K]; norm_num) (mul_nonneg (by dsimp [R]; norm_num) pos)))
  have c : (gap j:ℝ) ≤ scale j := by unfold scale; linarith
  apply step.trans
  calc
    _ ≤ (K*(R*scale j))^2 / 200 + 2^24*scale j*(K*(R*scale j)) := by gcongr
    _ ≤ (K*scale j)^2 := by
      dsimp [K,R]
      nlinarith only [sq_nonneg (scale j)]

/-- The entrance state may depend on every earlier choice. Conditional on
that state the new gap is uniform on its menu. Only the pointwise spectral
estimate for this menu is assumed; the law of the prefix is arbitrary. -/
theorem random_block_propagate {n : ℕ} (hn : 0 < n) (j : ℕ)
    {ι : Type*} [Fintype ι] (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (total : ∑ i, weight i = 1) (state : ι → RankPlacement n)
    (prior : (∑ i, weight i * RoughGapSelection.energy (state i)) ≤
      ((19*2^24) * scale (j+3))^2)
    (spectral : ∀ p : RankPlacement n,
      (∑ h ∈ ConsecutiveMenus.menu j, RoughGapSelection.energy (HarvestScaleNumbers.block j h p)) /
        (ConsecutiveMenus.menu j).card ≤
          RoughGapSelection.energy p / 200 + 2^24*(gap j:ℝ)*RoughGapSelection.mass p) :
    (∑ i, weight i * ((∑ h ∈ ConsecutiveMenus.menu j,
      RoughGapSelection.energy (HarvestScaleNumbers.block j h (state i))) /
        (ConsecutiveMenus.menu j).card)) ≤ ((19*2^24)*scale j)^2 := by
  let F i := RoughGapSelection.mass (state i)
  let Q i := RoughGapSelection.energy (state i)
  let U := ∑ i, weight i * F i
  have linear (a : ℝ) (f : ι → ℝ) :
      (∑ i, weight i * (a*f i)) = a * ∑ i, weight i * f i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have boundF : U ≤ Real.sqrt (∑ i,weight i*Q i) := by
    apply Real.le_sqrt_of_sq_le
    have one (i : ι) : (2*U)*F i ≤ Q i + U^2 := by
      nlinarith only [RoughGapSelection.mass_sq_le_energy hn (state i), sq_nonneg (F i - U),
        show RoughGapSelection.mass (state i) = F i from rfl,
        show RoughGapSelection.energy (state i) = Q i from rfl]
    have avg := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_left (one i) (hw i))
    rw [linear] at avg
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, total, one_mul] at avg
    change (2*U)*U ≤ _ at avg
    linarith
  apply propagate j prior
  calc
    _ ≤ ∑ i, weight i*(Q i/200 + 2^24*(gap j:ℝ)*F i) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (spectral (state i)) (hw i)
    _ = (∑ i,weight i*Q i)/200 + (2^24*(gap j:ℝ))*U := by
      simp only [mul_add,Finset.sum_add_distrib,linear,mul_div_assoc',← Finset.sum_div,U]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left boundF (by positivity))

/-- Exact rational calibration of the supplied spectral coefficients. -/
theorem spectral_coefficients :
    let D : ℝ := 460000
    let m : ℕ := 56
    let M : ℝ := 7/3
    let H : ℝ := 107/50
    ((2*m-1 : ℕ):ℝ)*M*4*H/D + 4*(1+D^2)/(2:ℝ)^m < 1/200 ∧
      M*H*(23/5)*D + ((2*m-1 : ℕ):ℝ)*M*(8*H^2+4*H/D) + 2*H < 2^24 := by
  norm_num

end Shellsort.ConsecutiveBlockBounds
