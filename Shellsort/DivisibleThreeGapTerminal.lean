import Shellsort.DivisibleThreeGapMatching

/-! The terminal case after two prescribed divisible leading gaps. -/
noncomputable section
namespace Shellsort.DivisibleThreeGapTerminal
open HarvestBlockIteration HarvestOperationalAudit PrescribedFirstGapLower PrescribedFirstGapTailMatching

theorem bounds {n H G : ℕ} (hg : 2≤G) (gh : G<H) (hn : H<n) (dv : G∣H) :
    let h : {j : ℕ // 0<j} := ⟨H,by omega⟩
    let g : {j : ℕ // 0<j} := ⟨G,by omega⟩
    let one : {j : ℕ // 0<j} := ⟨1,by decide⟩
    let t := (n:ℝ)*Real.logb 2 n + (n:ℝ)^2/H +
      (n:ℝ)*Real.sqrt ((n:ℝ)*H)/G + (n:ℝ)*Real.sqrt ((n:ℝ)*G)
    t ≤ 4104*meanComparisons n [h,g,one] ∧ meanComparisons n [h,g,one] ≤ 4*t := by
  let h : {j : ℕ // 0<j} := ⟨H,by omega⟩
  let g : {j : ℕ // 0<j} := ⟨G,by omega⟩
  let one : {j : ℕ // 0<j} := ⟨1,by decide⟩
  let a := (n:ℝ)*Real.logb 2 n
  let b := (n:ℝ)^2/H
  let d := (n:ℝ)*Real.sqrt ((n:ℝ)*H)/G
  let e := (n:ℝ)*Real.sqrt ((n:ℝ)*G)
  change a+b+d+e ≤ 4104*meanComparisons n [h,g,one] ∧
    meanComparisons n [h,g,one] ≤ 4*(a+b+d+e)
  have state : meanComparisons n [h,g,one] = meanComparisons n [h,g]+tailMean n G [one] :=
    DivisibleThreeGapMatching.split h g dv [one]
  have tailEq : tailMean n G [one] = uniformAverage (fun p : RankPlacement n =>
      (ordinaryWordComparisons (gapSort p G) [one]:ℝ)) := by simp only [tailMean,runWord_slots]
  constructor
  · have low := PrescribedTwoGapLower.uniform_lower (n:=n) h g (by omega : 2≤H) hn.le [one]
      (by intro y hy; obtain rfl := List.mem_singleton.mp hy; exact g.property)
      (by rfl)
    have fin := PrescribedTwoGapLower.after_first_capped (n:=n) hg (gh.trans hn).le
      (by decide : 0<1) [one]
      (by intro y hy; obtain rfl := List.mem_singleton.mp hy; rfl) (by rfl)
    simp only [Nat.cast_one,div_one,←tailEq] at fin
    change a+b+d ≤ 2056*meanComparisons n [h,g,one] at low
    change e ≤ 2048*tailMean n G [one] at fin
    have pos : 0 ≤ meanComparisons n [h,g] := uniformAverage_nonneg _ fun _ => by positivity
    linarith
  · have pre := TwoGapPrefixCost.two_pass_budget (n:=n) h g hn.le
    change _ ≤ (n:ℝ)^2/(4*H)+2*n+4*d at pre
    rw [show (n:ℝ)^2/(4*H)= b/4 by dsimp [b]; ring] at pre
    have tail : tailMean n G [one] ≤ 2*e+n := by
      have f := uniform_onePass_footrule_bound n G g.property
      have hs : (G:ℝ)≤Real.sqrt ((n:ℝ)*G) := by
        apply Real.le_sqrt_of_sq_le
        rw [sq]
        gcongr
        exact (gh.trans hn).le
      have foot : uniformAverage (fun p : RankPlacement n => footrule (gapSort p G)) ≤ 2*e := by
        apply f.trans
        dsimp [e]
        nlinarith [mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg n : (0:ℝ)≤n),
          mul_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n) (Real.sqrt_nonneg ((n:ℝ)*G))]
      rw [tailEq]
      have point (p : RankPlacement n) : (ordinaryWordComparisons (gapSort p G) [one]:ℝ) ≤
          footrule (gapSort p G) + n := by
        simp only [ordinaryWordComparisons,Nat.add_zero]
        have c := gapComparisonCost_upper (gapSort p G) 1 (by decide)
        have d := ordinaryInsertionCost_le_footrule (gapSort p G)
        exact (show (gapComparisonCost (gapSort p G) 1 (by decide):ℝ) ≤
          (gapInsertionCost (gapSort p G) 1 (by decide):ℝ) + n by exact_mod_cast c).trans
          (add_le_add_left d _)
      have av := uniformAverage_mono _ _ point
      rw [uniformAverage_add,uniformAverage_const] at av
      exact av.trans (add_le_add_left foot _)
    have lo : (1:ℝ) ≤ Real.logb 2 n := by
      rw [← Real.logb_self_eq_one (show (1:ℝ)<2 by norm_num)]
      exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by exact_mod_cast (show 2≤n by omega))
    have ac : (n:ℝ)≤a := le_mul_of_one_le_right (Nat.cast_nonneg _) lo
    have bn : 0≤b := by dsimp [b]; positivity
    have en : 0≤e := by dsimp [e]; positivity
    rw [state]
    linarith [Nat.cast_nonneg (α:=ℝ) n]

#print axioms bounds
end Shellsort.DivisibleThreeGapTerminal
