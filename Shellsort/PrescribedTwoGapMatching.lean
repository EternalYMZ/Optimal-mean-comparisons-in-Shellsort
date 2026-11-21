import Shellsort.PrescribedTwoGapUpper
import Shellsort.PrescribedTwoGapLower

/-! The minima over all legal continuations with a prescribed two-gap prefix,
in both accounting conventions, are sandwiched with universal constants. -/
noncomputable section
namespace Shellsort.PrescribedTwoGapMatching
open HarvestBlockIteration HarvestOperationalAudit PrescribedFirstGapLower PrescribedFirstGapTailMatching

theorem matching_bounds {n H G : ℕ} (hg : 2≤G) (gh : G<H) (hn : H<n) :
    let h : {k : ℕ // 0<k} := ⟨H,by omega⟩
    let g : {k : ℕ // 0<k} := ⟨G,by omega⟩
    let a := (n:ℝ)*Real.logb 2 n
    let b := (n:ℝ)^2/(H:ℝ)
    let d := (n:ℝ)*Real.sqrt ((n:ℝ)*H)/G
    (∀ v : PositiveWord, (∀ k ∈ v, k.val ≤ G) →
      ((g::v).map Subtype.val).getLast? = some 1 →
      a+b+d ≤ 2056*meanComparisons n (h::g::v) ∧
      a+d ≤ 34816*tailMean n H (g::v)) ∧
    ∃ w : PositiveWord,
      ((h::g::w).map Subtype.val).Pairwise (· > ·) ∧
      (∀ k∈h::g::w, k.val<n) ∧ ((h::g::w).map Subtype.val).getLast? = some 1 ∧
      w.length ≤ Nat.log 2 G ∧
      (∀ p : RankPlacement n, (runWord (slots p) (h::g::w)).1 = Vector.ofFn id) ∧
      tailMean n H (g::w) ≤ (2:ℝ)^167*(a+d) ∧
      meanComparisons n (h::g::w) ≤ (2:ℝ)^168*(a+b+d) := by
  let h : {k : ℕ // 0<k} := ⟨H,by omega⟩
  let g : {k : ℕ // 0<k} := ⟨G,by omega⟩
  refine ⟨?_,PrescribedTwoGapUpper.exists_continuation hg gh hn⟩
  intro v cap last
  refine ⟨PrescribedTwoGapLower.uniform_lower h g (by omega : 2≤H) hn.le v cap last,?_⟩
  apply PrescribedTwoGapLower.tailLower (by omega : 2≤H) hn.le g.property gh.le (g::v) _ last
  intro k hk
  rcases List.mem_cons.mp hk with rfl|hv
  · exact le_rfl
  · exact cap k hv

#print axioms matching_bounds
end Shellsort.PrescribedTwoGapMatching
