import Shellsort.PrescribedTwoGapMatching
import Shellsort.FirstPassUpper

/-! The comparisons actually spent in a prescribed two-pass prefix. -/
noncomputable section
namespace Shellsort.TwoGapPrefixCost
open HarvestBlockIteration HarvestOperationalAudit PrescribedFirstGapLower

theorem two_pass_budget {n : ℕ} (h g : {k : ℕ // 0<k}) (fits : h.val ≤ n) :
    meanComparisons n [h,g] ≤ (n:ℝ)^2/(4*h.val)+2*n+
      4*((n:ℝ)*Real.sqrt ((n:ℝ)*h.val)/g.val) := by
  have hs : (h.val:ℝ) ≤ Real.sqrt ((n:ℝ)*h.val) := by
    apply Real.le_sqrt_of_sq_le
    rw [sq]
    gcongr
  have f := uniform_onePass_footrule_bound n h.val h.property
  have geom := uniform_secondPassCost_geometry n h.val g.val g.property
  have j := uniformAverage_mono _ _ (fun p : RankPlacement n =>
    (show (gapComparisonCost (gapSort p h.val) g.val g.property:ℝ) ≤
      (gapInsertionCost (gapSort p h.val) g.val g.property:ℝ)+n by
      exact_mod_cast gapComparisonCost_upper (gapSort p h.val) g.val g.property))
  rw [uniformAverage_add,uniformAverage_const] at j
  have foot : uniformAverage (fun p : RankPlacement n => footrule (gapSort p h.val))
      ≤ 2*((n:ℝ)*Real.sqrt ((n:ℝ)*h.val)) := by
    apply f.trans
    nlinarith [mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg n : (0:ℝ)≤n),
      mul_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n) (Real.sqrt_nonneg ((n:ℝ)*h.val))]
  have gbound := geom.trans (mul_le_mul_of_nonneg_left foot (by positivity))
  have headBound := PrescribedFirstGapUpper.first_comparisons (n:=n) h
  rw [PrescribedFirstGapUpper.mean_head_tail]
  simp only [ordinaryWordComparisons,Nat.add_zero]
  apply (add_le_add headBound (j.trans (add_le_add_left gbound _))).trans
  apply le_of_eq
  ring

theorem last_one_bounds {n H : ℕ} (hh : 2≤H) (fits : H<n) :
    let h : {k : ℕ // 0<k} := ⟨H,by omega⟩
    let one : {k : ℕ // 0<k} := ⟨1,by decide⟩
    let a := (n:ℝ)*Real.logb 2 n + (n:ℝ)^2/H + (n:ℝ)*Real.sqrt ((n:ℝ)*H)
    a ≤ 2056*meanComparisons n [h,one] ∧ meanComparisons n [h,one] ≤ 4*a := by
  let h : {k : ℕ // 0<k} := ⟨H,by omega⟩
  let one : {k : ℕ // 0<k} := ⟨1,by decide⟩
  constructor
  · simpa only [one,div_one,Nat.cast_one] using
      PrescribedTwoGapLower.uniform_lower (n:=n) h one hh fits.le [] (by simp) (by rfl)
  · have upper := two_pass_budget (n:=n) h one fits.le
    change _ ≤ (n:ℝ)^2/(4*(H:ℝ))+2*n+4*((n:ℝ)*Real.sqrt ((n:ℝ)*H)/(1:ℝ)) at upper
    rw [div_one] at upper
    have lo : (1:ℝ) ≤ Real.logb 2 n := by
      rw [← Real.logb_self_eq_one (show (1:ℝ)<2 by norm_num)]
      exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by exact_mod_cast (show 2≤n by omega))
    have a := le_mul_of_one_le_right (Nat.cast_nonneg n : (0:ℝ)≤n) lo
    rw [show (n:ℝ)^2/(4*(H:ℝ)) = ((n:ℝ)^2/H)/4 by ring] at upper
    apply upper.trans
    nlinarith only [a, Nat.cast_nonneg (α:=ℝ) n, show 0 ≤ (n:ℝ)^2/H by positivity]

#print axioms last_one_bounds
end Shellsort.TwoGapPrefixCost
