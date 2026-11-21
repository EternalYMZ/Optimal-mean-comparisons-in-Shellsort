import Shellsort.VerifiedOptimum

/-! A reader-facing consumer of the formal result. Inputs below are indexed
by physical slot: q(i) is the key stored in slot i. -/
noncomputable section
open Shellsort Shellsort.HarvestOperationalAudit
namespace UserAudit

abbrev Word := List {h : ℕ // 0 < h}

def comparisonMean (n : ℕ) (w : Word) : ℝ :=
  (∑ q : Equiv.Perm (Fin n), ((runWord (Vector.ofFn fun i => q i) w).2 : ℝ)) /
    (n.factorial : ℝ)

theorem physical_mean (n : ℕ) (w : Word) :
    comparisonMean n w = PredeterminedOptimum.arrayMean n w := by
  let f (q : Equiv.Perm (Fin n)) := ((runWord (Vector.ofFn fun i => q i) w).2 : ℝ)
  have sumEq := Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin n))) f
  change (∑ q, f q) / _ = (∑ p : Equiv.Perm (Fin n), f p.symm) / _
  exact congrArg (fun x : ℝ => x / (n.factorial:ℝ)) sumEq.symm

/-- Every legal competitor is tested on the same uniformly distributed physical
arrays. Both correctness and cost are taken from the same runWord call. -/
theorem statement :
    ∃ W : ℕ → Word, ∀ n, 2 ≤ n →
      ((W n).map Subtype.val).Pairwise (· > ·) ∧
      (∀ h ∈ W n, h.val < n) ∧ ((W n).map Subtype.val).getLast? = some 1 ∧
      (∀ q : Equiv.Perm (Fin n), (runWord (Vector.ofFn fun i => q i) (W n)).1 = Vector.ofFn id) ∧
      (∀ v : Word, (v.map Subtype.val).Pairwise (· > ·) → (∀ h ∈ v, h.val < n) →
        (v.map Subtype.val).getLast? = some 1 → comparisonMean n (W n) ≤ comparisonMean n v) ∧
      (n:ℝ)*Real.logb 2 n/2 ≤ Real.logb 2 (n.factorial:ℝ) ∧
      Real.logb 2 (n.factorial:ℝ) ≤ comparisonMean n (W n) ∧
      comparisonMean n (W n) ≤ (1+(2:ℝ)^165)*(n:ℝ)*Real.logb 2 n := by
  obtain ⟨W, certificate⟩ := PredeterminedOptimum.exists_optimal_executed_family
  refine ⟨W, fun n hn => ?_⟩
  obtain ⟨hw, sorted, best, half, lo, hi⟩ := certificate n hn
  refine ⟨hw.1, hw.2.1, hw.2.2, fun q => sorted q.symm, ?_, half, ?_, ?_⟩
  · intro v h₁ h₂ h₃
    simpa only [physical_mean] using best v ⟨h₁,h₂,h₃⟩
  · simpa only [physical_mean] using lo
  · simpa only [physical_mean] using hi

#print axioms statement
end UserAudit
