import Shellsort.GapInsertionBridge

/-! Global and within-chain inversions paid for by a single gap pass. -/
namespace Shellsort.ResidueQuotientLower
open Finset

private def inv {n : ℕ} (q : Fin n → Fin n) (x y : Fin n) : ℕ :=
  if x < y ∧ q y < q x then 1 else 0

/-- Exchange an inverted pair a<b. Pair the other position pairs under
the same exchange so every comparison can be charged locally. -/
private theorem swap_pair {n : ℕ} (q : Fin n → Fin n) {a b : Fin n}
    (ab : a < b) (bad : q b < q a) (x y : Fin n) :
    let t := Equiv.swap a b
    inv (q ∘ t) x y + inv (q ∘ t) (t x) (t y) ≤ inv q x y + inv q (t x) (t y) := by
  dsimp [inv, Function.comp_def]
  simp only [Equiv.swap_apply_self]
  have cases_pos (z : Fin n) : z = a ∨ z = b ∨ (z ≠ a ∧ z ≠ b) := by tauto
  rcases cases_pos x with rfl | rfl | ⟨xa, xb⟩ <;>
    rcases cases_pos y with rfl | rfl | ⟨ya, yb⟩ <;>
    simp [Equiv.swap_apply_def, *] <;>
    split_ifs <;> omega

private def count {n : ℕ} (q : Fin n → Fin n) (keep : Fin n × Fin n → Bool) : ℕ :=
  ∑ xy : Fin n × Fin n, if keep xy then inv q xy.1 xy.2 else 0

private theorem exchange {n : ℕ} (q : Fin n → Fin n) (keep : Fin n × Fin n → Bool)
    {a b : Fin n} (ab : a < b) (bad : q b < q a)
    (sym : ∀ x y, keep (Equiv.swap a b x, Equiv.swap a b y) = keep (x,y)) :
    count (q ∘ Equiv.swap a b) keep ≤ count q keep ∧
      (keep (a,b) → count (q ∘ Equiv.swap a b) keep < count q keep) := by
  let t := Equiv.swap a b
  let t₂ := t.prodCongr t
  let term (f : Fin n → Fin n) (xy : Fin n × Fin n) :=
    if keep xy then inv f xy.1 xy.2 else 0
  have pair (xy : Fin n × Fin n) :
      term (q ∘ t) xy + term (q ∘ t) (t₂ xy) ≤ term q xy + term q (t₂ xy) := by
    rcases xy with ⟨x,y⟩
    dsimp [term,t₂,Equiv.prodCongr]
    rw [show keep (t x, t y) = keep (x,y) from sym x y]
    split
    · exact swap_pair q ab bad x y
    · rfl
  have twice (f : Fin n → Fin n) :
      ∑ xy, (term f xy + term f (t₂ xy)) = count f keep + count f keep := by
    rw [sum_add_distrib, t₂.sum_comp]
    rfl
  constructor
  · have h := sum_le_sum (s := univ) fun xy _ => pair xy
    rw [twice, twice] at h
    change count (q ∘ t) keep ≤ count q keep
    omega
  · intro active
    have strict : term (q ∘ t) (a,b) + term (q ∘ t) (t₂ (a,b)) <
        term q (a,b) + term q (t₂ (a,b)) := by
      have ba := sym a b
      simp only [Equiv.swap_apply_left, Equiv.swap_apply_right] at ba
      simp [term, t₂, t, inv, ba, active, ab, bad, not_lt_of_gt ab, not_lt_of_gt bad]
    have h := sum_lt_sum (s := univ) (fun xy _ => pair xy) ⟨(a,b), mem_univ _, strict⟩
    rw [twice, twice] at h
    change count (q ∘ t) keep < count q keep
    omega

private def within {n : ℕ} (e : ℕ) (xy : Fin n × Fin n) : Bool :=
  decide (xy.1.val % e = xy.2.val % e)

private theorem represented {n : ℕ} (p : RankPlacement n) (e : ℕ) :
    gapInversions p e = count p.symm (within e) := by
  rw [gapInversions_nat_pair_sum]
  conv_rhs => rw [count, Fintype.sum_prod_type, sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro i _
  by_cases same : i.val % e = j.val % e <;> simp [within, inv, same]

private theorem partition {n : ℕ} (p : RankPlacement n) (e : ℕ) :
    gapInversions p 1 = gapInversions p e + count p.symm (fun xy => !(within e xy)) := by
  rw [represented p 1, represented p e]
  unfold count
  rw [← sum_add_distrib]
  apply sum_congr rfl
  rintro ⟨i,j⟩ _
  by_cases same : i.val % e = j.val % e <;> simp [within, same, Nat.mod_one]

private theorem swap_residue {n e : ℕ} {a b : Fin n} (same : a.val % e = b.val % e) (x : Fin n) :
    (Equiv.swap a b x).val % e = x.val % e := by
  by_cases xa : x = a
  · subst x; simpa using same.symm
  by_cases xb : x = b
  · subst x; simpa using same
  simp [Equiv.swap_apply_of_ne_of_ne xa xb]

private theorem finished {n : ℕ} (p : RankPlacement n) (e : ℕ)
    (done : ¬ ∃ a b : Fin n, a < b ∧ p.symm b < p.symm a ∧ a.val % e = b.val % e) :
    gapSort p e = p ∧ gapInversions p e = 0 := by
  have increasing (x y : Fin n) (same : (p x).val % e = (p y).val % e)
      (xy : p x < p y) : x < y := by
    by_contra! fail
    have ne : y ≠ x := by rintro rfl; exact lt_irrefl _ xy
    have yx := lt_of_le_of_ne fail ne
    exact done ⟨p x, p y, xy, by simpa using yx, same⟩
  constructor
  · apply gapSort_unique
    · intro x; rfl
    intro x y same
    refine ⟨increasing x y same, fun xy => ?_⟩
    rcases lt_trichotomy (p x) (p y) with good | eq | rev
    · exact good
    · exact ((ne_of_lt xy) (p.injective eq)).elim
    · exact ((not_lt_of_gt xy) (increasing y x same.symm rev)).elim
  · rw [gapInversions_nat_pair_sum]
    apply sum_eq_zero
    intro j _
    apply sum_eq_zero
    intro i _
    exact ite_eq_right fun ⟨⟨lt,mod⟩, rev⟩ => done ⟨i,j,lt,rev,mod⟩

/-- Sorting the residue chains can only eliminate inversions between
different chains. Induct by exchanging an inverted pair in one chain. -/
private theorem cross_lower {n : ℕ} (e : ℕ) (p : RankPlacement n) :
    gapInversions (gapSort p e) 1 ≤ count p.symm (fun xy => !(within e xy)) := by
  by_cases has : ∃ a b : Fin n, a < b ∧ p.symm b < p.symm a ∧ a.val % e = b.val % e
  · obtain ⟨a,b,ab,bad,same⟩ := has
    let t := Equiv.swap a b
    let next := p.trans t
    have inverse : (next.symm : Fin n → Fin n) = p.symm ∘ t := by
      funext z; simp [next,t]
    have sym (x y : Fin n) : within e (t x,t y) = within e (x,y) := by
      simp [within,t,swap_residue same]
    have step := (exchange p.symm (within e) ab bad sym).2
      (show within e (a,b) by simp [within, same])
    have smaller : gapInversions next e < gapInversions p e := by
      rw [represented next e, represented p e, inverse]
      exact step
    have cross := (exchange p.symm (fun xy => !(within e xy)) ab bad
      (fun x y => congrArg (!·) (sym x y))).1
    have residue (x : Fin n) : (next x).val % e = (p x).val % e := swap_residue same _
    have final_eq : gapSort next e = gapSort p e := by
      apply gapSort_unique
      · intro x; rw [residue]; exact gapSort_preserves_residue p e x
      · intro x y h
        apply gapSort_sorted
        simpa only [gapSort_preserves_residue, ← residue] using h
    rw [← final_eq]
    apply (cross_lower e next).trans
    rw [inverse]
    exact cross
  · obtain ⟨fixed, zero⟩ := finished p e has
    rw [fixed, partition p e, zero, zero_add]
termination_by gapInversions p e

/-- Subtract the price of the entire gap pass from the original ordinary
inversion count. The bound holds for every size and gap. -/
theorem gap_sort_inversion_drop {n : ℕ} (p : RankPlacement n) (e : ℕ) :
    gapInversions (gapSort p e) 1 + gapInversions p e ≤ gapInversions p 1 := by
  rw [partition p e]
  have h := cross_lower e p
  omega

#print axioms gap_sort_inversion_drop

end Shellsort.ResidueQuotientLower
