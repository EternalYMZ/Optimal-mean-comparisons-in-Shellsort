import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace Shellsort.FiniteSourceBootstrap
open Finset

private theorem envelope_product (q i : ℕ) :
    q * (∏ j ∈ range i, q^(2^j)) = q^(2^i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [prod_range_succ, ← Nat.mul_assoc, ih, ← pow_add]
    congr 1
    rw [pow_succ]
    omega

/-- A zero-based sequence bounded at every step by q times its preceding
product has a doubly exponential envelope. No positivity premise is needed. -/
theorem product_envelope (q : ℕ) (m : ℕ → ℕ)
    (step : ∀ i, m i ≤ q * ∏ j ∈ range i, m j) (i : ℕ) :
    m i ≤ q^(2^i) := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    calc
      m i ≤ q * ∏ j ∈ range i, m j := step i
      _ ≤ q * ∏ j ∈ range i, q^(2^j) := by
        apply Nat.mul_le_mul_left
        apply prod_le_prod'
        exact fun j hj => ih j (mem_range.mp hj)
      _ = _ := envelope_product q i

#print axioms product_envelope
end Shellsort.FiniteSourceBootstrap
