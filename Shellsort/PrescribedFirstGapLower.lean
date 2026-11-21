import Shellsort.ComparisonWordLower
import Shellsort.FirstPassCostBounds

/-! Lower bounds on executed comparisons in any fixed word with a
prescribed initial gap. Costs are averaged over uniform rank permutations. -/
noncomputable section
namespace Shellsort.PrescribedFirstGapLower
open HarvestBlockIteration HarvestOperationalAudit

def meanComparisons (n : ℕ) (w : PositiveWord) : ℝ :=
  uniformAverage fun p : RankPlacement n => ((runWord (slots p) w).2 : ℝ)

private theorem operational (n : ℕ) (w : PositiveWord) :
    meanComparisons n w = uniformAverage (fun p : RankPlacement n => (ordinaryWordComparisons p w : ℝ)) := by
  simp only [meanComparisons,runWord_slots]

theorem mean_first_shifts_le (n : ℕ) (h : {k : ℕ // 0<k}) (tail : PositiveWord) :
    uniformAverage (fun p : RankPlacement n => (gapInsertionCost p h.val h.property : ℝ)) ≤
      meanComparisons n (h::tail) := by
  rw [operational]
  apply uniformAverage_mono
  intro p
  apply Nat.cast_le.mpr
  exact (gapComparisonCost_lower p h.val h.property).trans (Nat.le_add_right ..)

/-- The exact remainder in the first-pass shift count remains a valid
lower bound on the full word even when it does not end in gap 1. -/
theorem scaled_boundary_lower (n : ℕ) (h : {k : ℕ // 0<k}) (tail : PositiveWord) :
    (n:ℝ)^2 + ((n % h.val:ℕ):ℝ)*((h.val:ℝ)-((n % h.val:ℕ):ℝ)) ≤
      (h.val:ℝ)*(4*meanComparisons n (h::tail)+n) := by
  have eqn := uniform_firstPassCost_scaled_identity n h.val h.property
  have cost := mul_le_mul_of_nonneg_left (mean_first_shifts_le n h tail)
    (show 0 ≤ 4*(h.val:ℝ) by positivity)
  linarith

theorem entropy_and_head (n : ℕ) (h : {k : ℕ // 0<k}) (tail : PositiveWord)
    (last : ((h::tail).map Subtype.val).getLast? = some 1) :
    max (Real.logb 2 (n.factorial:ℝ)) ((n:ℝ)^2/(4*(h.val:ℝ))-(n:ℝ)/4) ≤
      meanComparisons n (h::tail) := by
  apply max_le
  · rw [operational]
    exact ComparisonAudit.word_mean_lower _ last
  · exact (uniform_firstPassCost_lower n h.val h.property).trans (mean_first_shifts_le n h tail)

/-- Uniform constant 1/8 for the prescribed-head objective, independent
of every other gap, including at finite n. -/
theorem uniform_sum_lower {n : ℕ} (hn : 2≤n) (h : {k : ℕ // 0<k}) (tail : PositiveWord)
    (last : ((h::tail).map Subtype.val).getLast? = some 1) :
    (n:ℝ)*Real.logb 2 n + (n:ℝ)^2/(h.val:ℝ) ≤ 8*meanComparisons n (h::tail) := by
  obtain ⟨entropy,head⟩ := max_le_iff.mp (entropy_and_head n h tail last)
  have first := (ComparisonTranscriptBound.half_nlog_le_log_factorial (n:=n) (by omega)).trans entropy
  have hlog : (1:ℝ) ≤ Real.logb 2 n := by
    rw [←Real.logb_self_eq_one (show (1:ℝ)<2 by norm_num)]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by exact_mod_cast hn)
  have low : (n:ℝ) ≤ (n:ℝ)*Real.logb 2 n := le_mul_of_one_le_right (Nat.cast_nonneg _) hlog
  have normalize : (n:ℝ)^2 / (4*(h.val:ℝ)) = ((n:ℝ)^2/(h.val:ℝ))/4 := by ring
  rw [normalize] at head
  linarith

#print axioms scaled_boundary_lower
#print axioms uniform_sum_lower
end Shellsort.PrescribedFirstGapLower
