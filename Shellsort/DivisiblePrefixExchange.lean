import Shellsort.HarvestOperationalAudit
import Shellsort.ModularCut

/-! Common checkpoints preserve differences in executed comparison cost. -/
namespace Shellsort.DivisiblePrefixExchange
open HarvestBlockIteration HarvestOperationalAudit

theorem run_append {α : Type} [LinearOrder α] {n : ℕ} (a : Vector α n)
    (u v : PositiveWord) :
    runWord a (u++v) =
      let first := runWord a u
      let tail := runWord first.1 v
      (tail.1,first.2+tail.2) := by
  induction u generalizing a with
  | nil => simp [runWord]
  | cons g u ih => simp only [List.cons_append,runWord,ih,Nat.add_assoc]

/-- Prefixes with identical physical output admit every common suffix,
and their difference in primary comparison counts is preserved exactly. -/
theorem common_state {α : Type} [LinearOrder α] {n : ℕ} (a : Vector α n)
    (u v w : PositiveWord) (eqState : (runWord a u).1 = (runWord a v).1) :
    (runWord a (u++w)).1 = (runWord a (v++w)).1 ∧
    (runWord a (u++w)).2 + (runWord a v).2 =
      (runWord a (v++w)).2 + (runWord a u).2 := by
  rw [run_append a u w,run_append a v w]
  simp only [eqState]
  exact ⟨trivial,by omega⟩

theorem canonical {n : ℕ} (p : RankPlacement n) (h : {k : ℕ // 0<k})
    (u : PositiveWord) (divides : ∀ g∈u, h.val∣g.val) :
    (runWord (slots p) (u++[h])).1 = slots (gapSort p h.val) := by
  rw [run_append,runWord_slots]
  simp only [runWord_slots, List.map_singleton, sortWord]
  apply congrArg slots
  apply gapSort_after_divisible_word
  intro x hx
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hx
  exact divides g hg

theorem prefix_exchange {n : ℕ} (p : RankPlacement n) (h : {k : ℕ // 0<k})
    (u v w : PositiveWord) (hu : ∀ g∈u, h.val∣g.val) (hv : ∀ g∈v, h.val∣g.val) :
    (runWord (slots p) ((u++[h])++w)).1 = (runWord (slots p) ((v++[h])++w)).1 ∧
    (runWord (slots p) ((u++[h])++w)).2 + (runWord (slots p) (v++[h])).2 =
      (runWord (slots p) ((v++[h])++w)).2 + (runWord (slots p) (u++[h])).2 :=
  common_state _ _ _ _ ((canonical p h u hu).trans (canonical p h v hv).symm)

#print axioms prefix_exchange
end Shellsort.DivisiblePrefixExchange
