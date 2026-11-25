import Shellsort.ConsecutiveMenus
import Shellsort.PredeterminedOptimum

/-! The schedule of consecutive triples, for any preselected menu choices. -/
namespace Shellsort.ConsecutiveMenus
open Actual214 HarvestTenSchedule

abbrev Choices := (j : ℕ) → {h // h ∈ menu j}

theorem choices_exist : Nonempty Choices := by
  classical
  have nonempty (j : ℕ) : (menu j).Nonempty := by
    apply Finset.card_pos.mp
    have := menu_density j
    have := gap_pos j
    omega
  exact ⟨fun j => ⟨(nonempty j).choose, (nonempty j).choose_spec⟩⟩

/-- The parameter k counts retained seeds, including terminal unmodified seeds. -/
def table (pick : Choices) : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [4,1]
  | j + 3 => gap (j+2) :: gap (j+1) :: (pick j).val :: table pick j

private theorem shape (pick : Choices) (k : ℕ) :
    (table pick k).length = k ∧ (table pick k).Pairwise (· > ·) ∧
    (∀ x ∈ table pick k, 0 < x ∧ x ≤ gap (k-1)) ∧
    (0 < k → (table pick k).getLast? = some 1) := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    match k with
    | 0 => simp [table]
    | 1 => simp [table,gap]
    | 2 => simp [table,gap,nextGap]
    | j+3 =>
      obtain ⟨len,order,members,last⟩ := ih j (by omega)
      have bounds := menu_order (pick j).property
      have retained : 2*gap (j+1) < gap (j+2) := (HarvestStageArithmetic.step (j+1)).1
      have mid : gap (j+1) < gap (j+2) := by omega
      have tail (x : ℕ) (hx : x ∈ table pick j) : x < (pick j).val := by
        cases j with
        | zero => simp [table] at hx
        | succ t => exact ((members x hx).2).trans_lt (bounds.2.2 t rfl)
      rw [table]
      refine ⟨by simp [len], ?_, ?_, ?_⟩
      · simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp]
        exact ⟨⟨mid, bounds.2.1.trans mid, fun x hx => (tail x hx).trans (bounds.2.1.trans mid)⟩,
          ⟨bounds.2.1, fun x hx => (tail x hx).trans bounds.2.1⟩,tail,order⟩
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | rfl | rfl | hx
        · exact ⟨gap_pos _,le_rfl⟩
        · exact ⟨gap_pos _,mid.le⟩
        · exact ⟨bounds.1,(bounds.2.1.trans mid).le⟩
        · exact ⟨(members x hx).1,((tail x hx).trans (bounds.2.1.trans mid)).le⟩
      · intro _
        simp only [List.getLast?_cons_cons]
        cases j with
        | zero =>
          have unique : menu 0 = {1} := by decide
          have hp := (pick 0).property
          have member : ∀ h : ℕ, h ∈ menu 0 → h = 1 := by simp [unique]
          simpa [table] using member _ hp
        | succ t =>
          cases eq : table pick (t+1) with
          | nil => simp [eq] at len
          | cons a as => simpa [eq] using last (Nat.succ_pos t)

/-- Every realization has the specified length, is legal, and sorts every
rank input. The distribution used to choose menu elements is unrestricted. -/
theorem realized_table {n : ℕ} (hn : 2 ≤ n) (pick : Choices) :
    let w := table pick (count n)
    w.length = count n ∧ w.length ≤ Nat.log 2 n ∧ w.Pairwise (· > ·) ∧
      (∀ h ∈ w, 0 < h ∧ h < n) ∧ w.getLast? = some 1 ∧
      ∀ p : RankPlacement n, sortWord p w = Equiv.refl _ := by
  intro w
  obtain ⟨length,order,members,last⟩ := shape pick (count n)
  have ends := last (count_positive n)
  refine ⟨length,length.le.trans (count_le_log hn),order,?_,ends,?_⟩
  · intro h hh
    have hh' := members h hh
    have up : h ≤ gap (top n) := by simpa [count] using hh'.2
    have := top_kept hn
    exact ⟨hh'.1,by omega⟩
  · exact fun p => HarvestTenLegal.sorted_if_last_one w p ends

end Shellsort.ConsecutiveMenus
