import Shellsort.PrescribedFirstGapLower
import Shellsort.StrictSuffixTransportLower
import Shellsort.PrescribedFirstGapTailMatching

/-! The checkpoint gap and the largest future gap are independent parameters.
The cost charged from the checkpoint includes the first subsequent pass. -/
noncomputable section
namespace Shellsort.PrescribedTwoGapLower
open HarvestBlockIteration HarvestOperationalAudit PrescribedFirstGapLower

theorem after_first_capped {n H G : ℕ} (hh : 2 ≤ H) (fits : H ≤ n)
    (positive : 0 < G) (v : PositiveWord)
    (cap : ∀ k ∈ v, k.val ≤ G) (last : (v.map Subtype.val).getLast? = some 1) :
    (n:ℝ) * Real.sqrt ((n:ℝ)*H) / G ≤ 2048 *
      uniformAverage (fun p : RankPlacement n => (ordinaryWordComparisons (gapSort p H) v : ℝ)) := by
  have point (p : RankPlacement n) : footrule (gapSort p H) ≤
      (2*(G:ℝ))*(ordinaryWordComparisons (gapSort p H) v : ℝ) := by
    have base := footrule_le_wordShiftDistance (gapSort p H) v
    rw [ComparisonAudit.sorted_last _ _ last] at base
    have zero : footrule (Equiv.refl (Fin n)) = 0 := by simp [footrule,transport]
    rw [zero,zero_add] at base
    linarith [StrictSuffixTransportLower.distance_le_cost (gapSort p H) v cap]
  have avg := uniformAverage_mono _ _ point
  rw [uniformAverage_const_mul] at avg
  have bound := (uniform_onePass_footrule_fluctuation_lower n H hh fits).trans avg
  apply (div_le_iff₀ (show (0:ℝ)<G by exact_mod_cast positive)).mpr
  linarith

theorem uniform_lower {n : ℕ} (h g : {k : ℕ // 0 < k})
    (hh : 2 ≤ h.val) (fits : h.val ≤ n) (v : PositiveWord)
    (cap : ∀ k ∈ v, k.val ≤ g.val) (last : ((g::v).map Subtype.val).getLast? = some 1) :
    (n:ℝ)*Real.logb 2 n + (n:ℝ)^2/(h.val:ℝ) + (n:ℝ)*Real.sqrt ((n:ℝ)*h.val)/g.val ≤
      2056*meanComparisons n (h::g::v) := by
  have allcap : ∀ k ∈ g::v, k.val ≤ g.val := by
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hm
    · exact le_rfl
    · exact cap k hm
  have head := uniform_sum_lower (n:=n) (by omega) h (g::v)
    (by simpa only [List.map_cons,List.getLast?_cons_cons] using last)
  have future := after_first_capped hh fits g.property (g::v) allcap last
  have subcost : uniformAverage (fun p : RankPlacement n =>
      (ordinaryWordComparisons (gapSort p h.val) (g::v) : ℝ)) ≤
      meanComparisons n (h::g::v) := by
    unfold meanComparisons
    apply uniformAverage_mono
    intro p
    rw [runWord_slots]
    apply Nat.cast_le.mpr
    exact Nat.le_add_left ..
  linarith

/-- The first pass was already paid. The whole remaining word has gap cap G. -/
theorem tailLower {n H G : ℕ} (hh : 2 ≤ H) (fits : H ≤ n)
    (positive : 0 < G) (order : G ≤ H) (v : PositiveWord)
    (cap : ∀ k ∈ v, k.val ≤ G) (last : (v.map Subtype.val).getLast? = some 1) :
    (n:ℝ)*Real.logb 2 n + (n:ℝ)*Real.sqrt ((n:ℝ)*H)/G ≤
      34816*PrescribedFirstGapTailMatching.tailMean n H v := by
  have information := PrescribedFirstGapTailMatching.uniform_lower hh fits v
    (fun k hk => (cap k hk).trans order) last
  have travel := after_first_capped hh fits positive v cap last
  have eqn : uniformAverage (fun p : RankPlacement n =>
      (ordinaryWordComparisons (gapSort p H) v:ℝ)) = PrescribedFirstGapTailMatching.tailMean n H v := by
    simp [PrescribedFirstGapTailMatching.tailMean,runWord_slots]
  rw [eqn] at travel
  linarith [show 0 ≤ (n:ℝ)*Real.sqrt ((n:ℝ)/H) by positivity]

#print axioms uniform_lower
#print axioms tailLower
end Shellsort.PrescribedTwoGapLower
