import Shellsort.TwoGapPrefixCost
import Shellsort.ModularCut

/-! Three prescribed leading gaps, the first a multiple of the second.
The two-pass prefix returns the exact same checkpoint as the second gap
alone, while both passes are charged in the executable comparison ledger. -/
noncomputable section
namespace Shellsort.DivisibleThreeGapMatching
open HarvestBlockIteration HarvestOperationalAudit PrescribedFirstGapLower PrescribedFirstGapTailMatching

theorem absorb {n H G : ℕ} (dv : G ∣ H) (p : RankPlacement n) :
    gapSort (gapSort p H) G = gapSort p G :=
  gapSort_after_divisible_word p [H] (by simpa using dv)

theorem split {n : ℕ} (h g : {j : ℕ // 0<j}) (dv : g.val ∣ h.val) (v : PositiveWord) :
    meanComparisons n (h::g::v) = meanComparisons n [h,g] + tailMean n g.val v := by
  simp only [meanComparisons,tailMean,runWord_slots,ordinaryWordComparisons,Nat.add_zero,
    Nat.cast_add,uniformAverage_add,absorb dv]
  ring

theorem matching_bounds {n H G K : ℕ} (kk : 2≤K) (kg : K<G) (gh : G<H) (hn : H<n)
    (dv : G ∣ H) :
    let h : {j : ℕ // 0<j} := ⟨H,by omega⟩
    let g : {j : ℕ // 0<j} := ⟨G,by omega⟩
    let k : {j : ℕ // 0<j} := ⟨K,by omega⟩
    let a := (n:ℝ)*Real.logb 2 n
    let b := (n:ℝ)^2/H
    let d := (n:ℝ)*Real.sqrt ((n:ℝ)*H)/G
    let e := (n:ℝ)*Real.sqrt ((n:ℝ)*G)/K
    (∀ v : PositiveWord, (∀ x∈v, x.val≤K) → ((k::v).map Subtype.val).getLast?=some 1 →
      a+b+d+e ≤ 4104*meanComparisons n (h::g::k::v)) ∧
    ∃ w : PositiveWord, ((h::g::k::w).map Subtype.val).Pairwise (· > ·) ∧
      (∀ x∈h::g::k::w, x.val<n) ∧ ((h::g::k::w).map Subtype.val).getLast?=some 1 ∧
      w.length ≤ Nat.log 2 K ∧
      (∀ p : RankPlacement n, (runWord (slots p) (h::g::k::w)).1 = Vector.ofFn id) ∧
      meanComparisons n (h::g::k::w) ≤ (2:ℝ)^168*(a+b+d+e) := by
  let h : {j : ℕ // 0<j} := ⟨H,by omega⟩
  let g : {j : ℕ // 0<j} := ⟨G,by omega⟩
  let k : {j : ℕ // 0<j} := ⟨K,by omega⟩
  let a := (n:ℝ)*Real.logb 2 n
  let b := (n:ℝ)^2/H
  let d := (n:ℝ)*Real.sqrt ((n:ℝ)*H)/G
  let e := (n:ℝ)*Real.sqrt ((n:ℝ)*G)/K
  constructor
  · intro v cap last
    have ck : ∀ x∈k::v, x.val≤K := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl|hv
      · exact le_rfl
      · exact cap x hv
    have first := PrescribedTwoGapLower.uniform_lower (n:=n) h g (by omega : 2≤H) hn.le
      (k::v) (fun x hx => (ck x hx).trans kg.le)
      (by simpa only [List.map_cons,List.getLast?_cons_cons] using last)
    have move := PrescribedTwoGapLower.after_first_capped (n:=n) (by omega : 2≤G)
      (gh.trans hn).le k.property (k::v) ck last
    have cost : uniformAverage (fun p : RankPlacement n =>
        (ordinaryWordComparisons (gapSort p G) (k::v):ℝ)) ≤ meanComparisons n (h::g::k::v) := by
      rw [split h g dv]
      have idn : uniformAverage (fun p : RankPlacement n =>
          (ordinaryWordComparisons (gapSort p G) (k::v):ℝ)) = tailMean n G (k::v) := by
        simp only [tailMean,runWord_slots]
      rw [idn]
      apply le_add_of_nonneg_left
      exact uniformAverage_nonneg _ fun _ => by positivity
    change a+b+d ≤ 2056*meanComparisons n (h::g::k::v) at first
    change e ≤ 2048*_ at move
    change a+b+d+e ≤ 4104*meanComparisons n (h::g::k::v)
    linarith
  · obtain ⟨w,ord,admissible,last,len,sorts,tail,_⟩ :=
      PrescribedTwoGapUpper.exists_continuation (n:=n) kk kg (gh.trans hn)
    refine ⟨w,?_,?_,?_,len,?_,?_⟩
    · apply List.pairwise_cons.mpr
      refine ⟨?_,ord⟩
      intro x hx
      change x∈G::(k::w).map Subtype.val at hx
      rcases List.mem_cons.mp hx with rfl|hs
      · exact gh
      · exact ((List.pairwise_cons.mp ord).1 x hs).trans gh
    · intro x hx
      rcases List.mem_cons.mp hx with rfl|hs
      · exact hn
      · exact admissible x hs
    · exact last
    · intro p
      have lastFull : ((h::g::k::w).map Subtype.val).getLast? = some 1 := last
      rw [runWord_slots, ComparisonAudit.sorted_last _ _ lastFull]
      rfl
    · change meanComparisons n (h::g::k::w) ≤ (2:ℝ)^168*(a+b+d+e)
      rw [split h g dv]
      have p := TwoGapPrefixCost.two_pass_budget (n:=n) h g hn.le
      change meanComparisons n [h,g] ≤ (n:ℝ)^2/(4*(H:ℝ))+2*n+4*d at p
      rw [show (n:ℝ)^2/(4*(H:ℝ)) = b/4 by dsimp [b]; ring] at p
      change tailMean n G (k::w) ≤ (2:ℝ)^167*(a+e) at tail
      have lo : (1:ℝ) ≤ Real.logb 2 n := by
        rw [← Real.logb_self_eq_one (show (1:ℝ)<2 by norm_num)]
        exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by exact_mod_cast (show 2≤n by omega))
      have an : (n:ℝ)≤a := le_mul_of_one_le_right (Nat.cast_nonneg _) lo
      have bn : 0≤b := by dsimp [b]; positivity
      have dn : 0≤d := by dsimp [d]; positivity
      have en : 0≤e := by dsimp [e]; positivity
      apply (add_le_add p tail).trans
      nlinarith only [an,bn,dn,en,Nat.cast_nonneg (α:=ℝ) n]

#print axioms matching_bounds
end Shellsort.DivisibleThreeGapMatching
