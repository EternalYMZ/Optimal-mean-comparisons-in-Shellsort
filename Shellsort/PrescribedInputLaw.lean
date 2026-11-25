import Shellsort.HarvestOperationalAudit
import Shellsort.PredeterminedOptimum

/-! Finite averaging for prescribed input laws. The pointwise expected cost
of the supplied input-independent table distribution is an explicit premise. -/
noncomputable section
namespace Shellsort.PrescribedInputLaw
open Finset HarvestBlockIteration HarvestOperationalAudit

/-- A support witness for a prescribed law on rank inputs. The table index
may depend on the law. The cost is the measured slot-array comparison count. -/
theorem exists_short_table {n : ℕ} {ι : Type*} [Fintype ι]
    (W : ι → PositiveWord) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (total : ∑ i, weight i = 1)
    (legal : ∀ i, 0 < weight i → PredeterminedOptimum.Legal n (W i))
    (short : ∀ i, 0 < weight i → (W i).length ≤ Nat.log 2 n)
    (B : ℝ) (bound : ∀ p : RankPlacement n,
      ∑ i, weight i * ((runWord (slots p) (W i)).2 : ℝ) ≤ B)
    (law : RankPlacement n → ℝ) (nonneg : ∀ p, 0 ≤ law p) (normalized : ∑ p, law p = 1) :
    ∃ i, 0 < weight i ∧ PredeterminedOptimum.Legal n (W i) ∧ (W i).length ≤ Nat.log 2 n ∧
      ∑ p, law p * ((runWord (slots p) (W i)).2 : ℝ) ≤ B := by
  classical
  let cost (i : ι) (p : RankPlacement n) : ℝ := (runWord (slots p) (W i)).2
  let mean (i : ι) := ∑ p, law p * cost i p
  have swap : (∑ i, weight i * mean i) = ∑ p, law p * ∑ i, weight i * cost i p := by
    simp only [mean, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun p _ => sum_congr rfl fun i _ => by ring
  have avg : (∑ i, weight i * mean i) ≤ B := calc
    _ = _ := swap
    _ ≤ ∑ p, law p * B := sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (bound p) (nonneg p)
    _ = B := by rw [← sum_mul,normalized,one_mul]
  have support : ∃ i, 0 < weight i := by
    by_contra! h
    have zero : ∀ i, weight i = 0 := fun i => le_antisymm (h i) (hw i)
    simp [zero] at total
  obtain ⟨i,hi⟩ := support
  by_contra! absurd
  have worse (k : ι) (hk : 0 < weight k) : B < mean k :=
    absurd k hk (legal k hk) (short k hk)
  have strict : (∑ k, weight k * B) < ∑ k, weight k * mean k := by
    apply sum_lt_sum
    · intro k _
      by_cases hp : 0 < weight k
      · exact mul_le_mul_of_nonneg_left (worse k hp).le (hw k)
      · simp [le_antisymm (le_of_not_gt hp) (hw k)]
    · exact ⟨i,mem_univ _,mul_lt_mul_of_pos_left (worse i hi) hi⟩
  rw [← sum_mul, total, one_mul] at strict
  exact (not_lt_of_ge avg) strict

end Shellsort.PrescribedInputLaw
