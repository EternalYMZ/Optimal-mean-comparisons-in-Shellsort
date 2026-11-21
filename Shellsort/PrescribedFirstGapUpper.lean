import Shellsort.PrescribedFirstGapLower
import Shellsort.WarmRestart

/-! Fix the first gap before drawing the uniform input. The witness is one
strictly descending continuation for that pair of size and first gap. Both
inequalities concern executed linear-insertion key comparisons. -/
noncomputable section
namespace Shellsort.PrescribedFirstGapUpper
open HarvestBlockIteration HarvestOperationalAudit PrescribedFirstGapLower

theorem first_comparisons {n : ℕ} (h : {k : ℕ // 0<k}) :
    uniformAverage (fun p : RankPlacement n => (gapComparisonCost p h.val h.property : ℝ)) ≤
      (n:ℝ)^2/(4*(h.val:ℝ))+n := by
  have a := uniformAverage_mono _ _ (fun p : RankPlacement n =>
    (show (gapComparisonCost p h.val h.property:ℝ) ≤ (gapInsertionCost p h.val h.property:ℝ)+n
      by exact_mod_cast gapComparisonCost_upper p h.val h.property))
  rw [uniformAverage_add,uniformAverage_const] at a
  exact a.trans (add_le_add_left (uniform_firstPassCost_upper n h.val h.property) _)

theorem mean_head_tail (n : ℕ) (h : {k : ℕ // 0<k}) (w : PositiveWord) :
    meanComparisons n (h::w) =
      uniformAverage (fun p : RankPlacement n => (gapComparisonCost p h.val h.property:ℝ)) +
      uniformAverage (fun p : RankPlacement n => (ordinaryWordComparisons (gapSort p h.val) w:ℝ)) := by
  simp only [meanComparisons, runWord_slots, ordinaryWordComparisons, Nat.cast_add, uniformAverage_add]

/-- The lower estimate covers every continuation ending in one. The same
order of growth is attained by a legal word with this prescribed head. -/
theorem matching_bounds {n H : ℕ} (hH : 2≤H) (hN : H<n) :
    let h : {k : ℕ // 0<k} := ⟨H,by omega⟩
    let target := (n:ℝ)*Real.logb 2 n + (n:ℝ)^2/(H:ℝ)
    (∀ v : PositiveWord, ((h::v).map Subtype.val).getLast? = some 1 →
      target ≤ 8*meanComparisons n (h::v)) ∧
    ∃ w : PositiveWord,
      ((h::w).map Subtype.val).Pairwise (· > ·) ∧
      (∀ k ∈ h::w, k.val < n) ∧
      ((h::w).map Subtype.val).getLast? = some 1 ∧
      (∀ p : RankPlacement n, (runWord (slots p) (h::w)).1 = Vector.ofFn id) ∧
      w.length ≤ Nat.log 2 H ∧
      meanComparisons n (h::w) ≤ (2:ℝ)^174*target := by
  let h : {k : ℕ // 0<k} := ⟨H,by omega⟩
  change (∀ v : PositiveWord, _ → _ ≤ 8*meanComparisons n (h::v)) ∧ _
  constructor
  · intro v last
    exact uniform_sum_lower (by omega) h v last
  let P : RankPlacement n → RankPlacement n := fun p => gapSort p H
  obtain ⟨w,_,cap,desc,last,sorted,len,pay⟩ :=
    WarmRestart.exists_strict_suffix (by omega : 0<n) hH P
  have hR : (0:ℝ)<H := by exact_mod_cast (by omega : 0<H)
  have lnle : Real.logb 2 H ≤ Real.logb 2 n :=
    Real.logb_le_logb_of_le (by norm_num) hR (by exact_mod_cast hN.le)
  have one : (1:ℝ) ≤ Real.logb 2 n := by
    rw [← Real.logb_self_eq_one (show (1:ℝ)<2 by norm_num)]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by exact_mod_cast (by omega : 2≤n))
  have absorb : (n:ℝ) ≤ n*Real.logb 2 n :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) one
  have root : Real.sqrt (meanEnergy P) ≤ (2:ℝ)^115*n := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity,initial_bound (by omega) P⟩
  have tail : uniformAverage (fun p => (ordinaryWordComparisons (P p) w:ℝ)) ≤
      (1+(2:ℝ)^165)*n*Real.logb 2 n+(2:ℝ)^172*((n:ℝ)^2/H) := by
    apply pay.trans
    apply add_le_add
    · gcongr
    · calc
        _ ≤ (2:ℝ)^57*(((2:ℝ)^115*n)/(H:ℝ))*n := by gcongr
        _ = _ := by ring
  refine ⟨w,desc,?_,?_,?_,len,?_⟩
  · intro k hk
    rcases List.mem_cons.mp hk with rfl | kw
    · exact hN
    · have := cap k kw
      omega
  · cases w with
    | nil => simp at last
    | cons => exact last
  · intro p
    rw [runWord_slots]
    change slots (sortWord (gapSort p H) (w.map Subtype.val)) = _
    rw [sorted]
    rfl
  · rw [mean_head_tail]
    have first := first_comparisons (n:=n) h
    change _ ≤ (n:ℝ)^2/(4*(H:ℝ))+n at first
    change _ ≤ (2:ℝ)^174*((n:ℝ)*Real.logb 2 n+(n:ℝ)^2/H)
    have bound := add_le_add first tail
    apply bound.trans
    have a : 0≤(n:ℝ)*Real.logb 2 n := (Nat.cast_nonneg _).trans absorb
    have b : 0≤(n:ℝ)^2/(H:ℝ) := by positivity
    rw [show (n:ℝ)^2/(4*(H:ℝ))=((n:ℝ)^2/(H:ℝ))/4 by ring]
    nlinarith only [absorb,a,b]

#print axioms first_comparisons
#print axioms matching_bounds
end Shellsort.PrescribedFirstGapUpper
