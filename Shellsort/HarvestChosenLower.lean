import Shellsort.HarvestTenLegal
import Shellsort.HarvestBlockComparisonSum
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! A pointwise comparison lower bound for the same ten-center realisations.
It uses only the first retained gap, number of passes, and insertion scans. -/
noncomputable section
namespace Shellsort.HarvestChosenLower
open Actual214 HarvestTenLegal HarvestTenSchedule HarvestStageArithmetic
open HarvestBlockIteration HarvestMenuBlock

/-- A perturbed gap is always the third entry of its stage. In every case,
including an all-tail word, the leading gap is the unperturbed top center. -/
private theorem first_center (k:ℕ) (hk:0<k) (hs:List ℕ)
    (picks:List.Forall₂ (fun s h => h∈choices s.j) (stages k) hs) :
    ∃ rest, realizedWord (stages k) hs ++ tailWord k = gap (k-1)::rest := by
  by_cases e:eligible k
  · have ss : stages k=chunk k :: stages (k-10) := by rw [stages_eq]; simp [e]
    rw [ss] at picks ⊢
    cases picks with
    | cons pick rem =>
      have eq : k-3+2=k-1 := by have := e.1; omega
      simp [realizedWord,stageWord,chunk,eq]
  · have ss : stages k=[] := by rw [stages_eq]; simp [e]
    rw [ss] at picks ⊢
    cases picks
    have tail : tailCount k=k := by rw [tailCount_eq]; simp [e]
    change ∃ rest, (List.range (tailCount k)).reverse.map gap = gap (k-1)::rest
    rw [tail]
    obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    refine ⟨(List.range l).reverse.map gap,?_⟩
    simp [List.range_succ]

theorem chosen_gap_half {n:ℕ} (hn:2≤n) (hs:List ℕ)
    (picks:List.Forall₂ (fun s h => h∈choices s.j) (stages (count n)) hs)
    (k:ℕ) (hk:k∈realizedWord (stages (count n)) hs ++ tailWord (count n)) :
    2*k ≤ n := by
  have p := (full_word_legal hn hs picks).1
  obtain ⟨rest,eq⟩ := first_center (count n) (count_positive _) hs picks
  rw [eq] at hk p
  have hi := top_kept hn
  have bound : k ≤ gap (top n) := by
    rcases List.mem_cons.mp hk with same|mem
    · simpa [count] using same.le
    · simpa [count] using ((List.pairwise_cons.mp p).1 k mem).le
  omega

theorem log_le_passes {n : ℕ} (hn:2≤n) : Real.logb 2 n ≤ 3*(count n:ℝ) := by
  let k := count n
  have kp : 0<k := count_positive _
  have upper : gap k ≤ 4^k := by simpa [gap] using four_growth 0 k
  have two : n < 2*4^k := (next_excluded hn).trans_le (Nat.mul_le_mul_left 2 upper)
  have exactPow : 2*4^k=2^(2*k+1) := by rw [pow_succ,Nat.mul_comm, pow_mul]; norm_num
  have size : (n:ℝ) ≤ (2:ℝ)^(2*k+1) := by exact_mod_cast (two.le.trans_eq exactPow)
  have l := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (show (0:ℝ)<n by exact_mod_cast (show 0<n by omega)) size
  rw [Real.logb_pow,Real.logb_self_eq_one (by norm_num),mul_one] at l
  push_cast at l
  change Real.logb 2 n ≤ 3*(k:ℝ)
  have kr : (1:ℝ)≤k := by exact_mod_cast kp
  linarith

private theorem enough_visits {n:ℕ} (p:RankPlacement n) (w:PositiveWord)
    (half:∀ h∈w, 2*h.val ≤ n) :
    n*w.length ≤ 2*ordinaryWordComparisons p w := by
  induction w generalizing p with
  | nil => simp [ordinaryWordComparisons]
  | cons h w ih =>
    have cap := half h List.mem_cons_self
    have scan := (max_le_iff.mp (gapComparisonCost_scan_bounds p h.val h.property).1).2
    have pay : n ≤ 2 * gapComparisonCost p h.val h.property := by omega
    have tail := ih (gapSort p h.val) (fun x hx => half x (List.mem_cons_of_mem _ hx))
    simp only [List.length_cons,Nat.mul_succ,ordinaryWordComparisons,Nat.mul_add]
    omega

/-- For each permutation, the same emitted word used by the upper theorem
already performs at least n log₂ n / 6 physical key comparisons. -/
theorem chosen_pointwise_lower {n:ℕ} (hn:2≤n) (hs:List ℕ)
    (picks:List.Forall₂ (fun s h => h∈choices s.j) (stages (count n)) hs)
    (w:PositiveWord)
    (word:w.map Subtype.val = realizedWord (stages (count n)) hs ++ tailWord (count n))
    (length:w.length=count n) (p:RankPlacement n) :
    (n:ℝ)*Real.logb 2 n/6 ≤ (ordinaryWordComparisons p w:ℝ) := by
  have half (h) (hh : h∈w) : 2*h.val≤n :=
    chosen_gap_half hn hs picks h.val (word ▸ List.mem_map_of_mem (f:=Subtype.val) hh)
  have visits := enough_visits p w half
  rw [length] at visits
  have rc : (n:ℝ)*(count n:ℝ) ≤ 2*(ordinaryWordComparisons p w:ℝ) := by exact_mod_cast visits
  have lb := mul_le_mul_of_nonneg_left (log_le_passes hn) (Nat.cast_nonneg (α:=ℝ) n)
  linarith

theorem chosen_mean_lower {n:ℕ} (hn:2≤n) (hs:List ℕ)
    (picks:List.Forall₂ (fun s h => h∈choices s.j) (stages (count n)) hs)
    (w:PositiveWord)
    (word:w.map Subtype.val = realizedWord (stages (count n)) hs ++ tailWord (count n))
    (length:w.length=count n) :
    (n:ℝ)*Real.logb 2 n/6 ≤ uniformAverage (fun p : RankPlacement n => (ordinaryWordComparisons p w:ℝ)) := by
  rw [← uniformAverage_const n ((n:ℝ)*Real.logb 2 n/6)]
  exact uniformAverage_mono _ _ (chosen_pointwise_lower hn hs picks w word length)

#print axioms chosen_pointwise_lower
#print axioms chosen_mean_lower
end Shellsort.HarvestChosenLower
