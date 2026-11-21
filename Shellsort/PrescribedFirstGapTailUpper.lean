import Shellsort.PrescribedFirstGapUpper
import Shellsort.FirstGapMeanEnergy

/-! Start the continuation at the actual first-pass distribution. The same
chosen word sorts all inputs, and its mean cost is the executed comparison
counter on the unmodified state produced by the ordinary first pass. -/
noncomputable section
namespace Shellsort.PrescribedFirstGapTailUpper
open HarvestBlockIteration HarvestOperationalAudit

theorem exists_tail {n H : ℕ} (hH : 2≤H) (hN : H<n) :
    ∃ w : PositiveWord, (H::w.map Subtype.val).Pairwise (· > ·) ∧
      (w.map Subtype.val).getLast? = some 1 ∧ w.length ≤ Nat.log 2 H ∧
      (∀ p : RankPlacement n, (runWord (slots (gapSort p H)) w).1 = Vector.ofFn id) ∧
      uniformAverage (fun p : RankPlacement n => ((runWord (slots (gapSort p H)) w).2:ℝ)) ≤
        (1+(2:ℝ)^165)*n*Real.logb 2 H+(2:ℝ)^58*n*Real.sqrt ((n:ℝ)/H) := by
  let P : RankPlacement n → RankPlacement n := fun p => gapSort p H
  obtain ⟨w,_,_,order,last,sorted,len,cost⟩ :=
    WarmRestart.exists_strict_suffix (by omega : 0<n) hH P
  have hp : (0:ℝ)<H := by exact_mod_cast (by omega : 0<H)
  have en : meanEnergy P ≤ 2*(n:ℝ)*H :=
    FirstGapMeanEnergy.first_gap_energy_upper (by omega) hN.le
  have root : Real.sqrt (meanEnergy P)/(H:ℝ) ≤ 2*Real.sqrt ((n:ℝ)/H) := by
    apply (div_le_iff₀ hp).mpr
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity)]
    calc
      _ ≤ 2*(n:ℝ)*H := en
      _ ≤ 4*(n:ℝ)*H := by gcongr <;> norm_num
      _ = _ := by field_simp; ring
  refine ⟨w,order,last,len,fun p => ?_,?_⟩
  · rw [runWord_slots, sorted]
    rfl
  · simp only [runWord_slots]
    apply cost.trans
    refine add_le_add le_rfl ?_
    calc
      _ ≤ (2:ℝ)^57*(2*Real.sqrt ((n:ℝ)/H))*n := by gcongr
      _ = _ := by ring

#print axioms exists_tail
end Shellsort.PrescribedFirstGapTailUpper
