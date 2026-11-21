import Shellsort.PrescribedFirstGapTailMatching

/-! A fixed physical prefix of two gaps, followed by a common decreasing
continuation chosen before the uniformly random input. -/
noncomputable section
namespace Shellsort.PrescribedTwoGapUpper
open HarvestBlockIteration HarvestOperationalAudit PrescribedFirstGapLower
open PrescribedFirstGapUpper PrescribedFirstGapTailMatching

private theorem second_comparisons {n G : ℕ} (hn : 0<n) (g : 0<G)
    (P : RankPlacement n → RankPlacement n) :
    uniformAverage (fun p => (gapComparisonCost (P p) G g:ℝ)) ≤
      n + (2/(G:ℝ))*Real.sqrt (meanEnergy P)*n := by
  have s := RoughGapSelection.prefix_mean_comparisons hn g P
  simp_rw [div_eq_inv_mul] at s
  rw [uniformAverage_const_mul, ←div_eq_inv_mul] at s
  have d := (div_le_iff₀ (by exact_mod_cast hn : (0:ℝ)<n)).mp s
  apply d.trans_eq
  unfold meanEnergy
  ring

/-- The same continuation witnesses both the total and the cost that
remains after the first of the two prescribed passes. -/
theorem exists_continuation {n H G : ℕ} (hg : 2≤G) (gh : G<H) (hn : H<n) :
    let h : {k : ℕ // 0<k} := ⟨H,by omega⟩
    let g : {k : ℕ // 0<k} := ⟨G,by omega⟩
    let a := (n:ℝ)*Real.logb 2 n
    let b := (n:ℝ)^2/(H:ℝ)
    let d := (n:ℝ)*Real.sqrt ((n:ℝ)*H)/G
    ∃ w : PositiveWord,
      ((h::g::w).map Subtype.val).Pairwise (· > ·) ∧
      (∀ k∈h::g::w, k.val<n) ∧ ((h::g::w).map Subtype.val).getLast? = some 1 ∧
      w.length ≤ Nat.log 2 G ∧
      (∀ p : RankPlacement n, (runWord (slots p) (h::g::w)).1 = Vector.ofFn id) ∧
      tailMean n H (g::w) ≤ (2:ℝ)^167*(a+d) ∧
      meanComparisons n (h::g::w) ≤ (2:ℝ)^168*(a+b+d) := by
  let h : {k : ℕ // 0<k} := ⟨H,by omega⟩
  let g : {k : ℕ // 0<k} := ⟨G,by omega⟩
  let P : RankPlacement n → RankPlacement n := fun p => gapSort p H
  let Q : RankPlacement n → RankPlacement n := fun p => gapSort (P p) G
  let a := (n:ℝ)*Real.logb 2 n
  let b := (n:ℝ)^2/(H:ℝ)
  let d := (n:ℝ)*Real.sqrt ((n:ℝ)*H)/G
  change ∃ w : PositiveWord, _ ∧ _ ∧ _ ∧ _ ∧ _ ∧
    tailMean n H (g::w) ≤ (2:ℝ)^167*(a+d) ∧
    meanComparisons n (h::g::w) ≤ (2:ℝ)^168*(a+b+d)
  have pos : (0:ℝ)<G := by exact_mod_cast g.property
  have en : meanEnergy P ≤ 2*(n:ℝ)*H :=
    FirstGapMeanEnergy.first_gap_energy_upper h.property hn.le
  have rms : Real.sqrt (meanEnergy P) ≤ 2*Real.sqrt ((n:ℝ)*H) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    rw [mul_pow,Real.sq_sqrt (by positivity)]
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n) (Nat.cast_nonneg H : (0:ℝ)≤H)]
  have noninc : meanEnergy Q ≤ meanEnergy P := word_mean_le P [G]
  have rmsQ := (Real.sqrt_le_sqrt noninc).trans rms
  have payG : uniformAverage (fun p => (gapComparisonCost (P p) G g.property:ℝ))
      ≤ n+4*d := by
    apply (second_comparisons (by omega) g.property P).trans
    calc
      _ ≤ n+(2/(G:ℝ))*(2*Real.sqrt ((n:ℝ)*H))*n := by gcongr
      _ = _ := by dsimp [d]; ring
  obtain ⟨w,_,cap,order,last,sorts,len,budget⟩ :=
    WarmRestart.exists_strict_suffix (by omega : 0<n) hg Q
  have l : Real.logb 2 G ≤ Real.logb 2 n :=
    Real.logb_le_logb_of_le (by norm_num) pos (by exact_mod_cast (show G≤n by omega))
  have one : (1:ℝ) ≤ Real.logb 2 n := by
    rw [← Real.logb_self_eq_one (show (1:ℝ)<2 by norm_num)]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by exact_mod_cast (show 2≤n by omega))
  have absorb : (n:ℝ) ≤ a := le_mul_of_one_le_right (Nat.cast_nonneg _) one
  have an := (Nat.cast_nonneg n : (0:ℝ)≤n).trans absorb
  have dn : 0≤d := by dsimp [d]; positivity
  have bn : 0≤b := by dsimp [b]; positivity
  have tail : uniformAverage (fun p => (ordinaryWordComparisons (Q p) w:ℝ)) ≤
      (1+(2:ℝ)^165)*a+(2:ℝ)^58*d := by
    apply budget.trans
    calc
      _ ≤ (1+(2:ℝ)^165)*n*Real.logb 2 n +
          (2:ℝ)^57*((2*Real.sqrt ((n:ℝ)*H))/(G:ℝ))*n := by gcongr
      _ = _ := by dsimp [a,d]; ring
  have both : tailMean n H (g::w) ≤ (2:ℝ)^167*(a+d) := by
    have split : tailMean n H (g::w) =
        uniformAverage (fun p => (gapComparisonCost (P p) G g.property:ℝ)) +
        uniformAverage (fun p => (ordinaryWordComparisons (Q p) w:ℝ)) := by
      simp only [tailMean,runWord_slots,ordinaryWordComparisons,Nat.cast_add,uniformAverage_add]
      rfl
    rw [split]
    apply (add_le_add payG tail).trans
    nlinarith only [absorb,an,dn]
  refine ⟨w,?_,?_,?_,len,?_,both,?_⟩
  · apply List.pairwise_cons.mpr
    refine ⟨?_,order⟩
    intro x hx
    change x ∈ G::w.map Subtype.val at hx
    rcases List.mem_cons.mp hx with rfl|hx
    · exact gh
    · exact (List.pairwise_cons.mp order).1 x hx |>.trans gh
  · intro k hk
    rcases List.mem_cons.mp hk with rfl|hk
    · exact hn
    rcases List.mem_cons.mp hk with rfl|hk
    · exact gh.trans hn
    · have := cap k hk
      omega
  · cases w with
    | nil => simp at last
    | cons => exact last
  · intro p
    rw [runWord_slots]
    change slots (sortWord (Q p) (w.map Subtype.val)) = Vector.ofFn id
    rw [sorts]
    rfl
  · rw [mean_head_tail]
    have first := first_comparisons (n:=n) h
    have fe : (n:ℝ)^2/(4*(h.val:ℝ))=b/4 := by dsimp [h,b]; ring
    rw [fe] at first
    have bt : uniformAverage (fun p : RankPlacement n => (ordinaryWordComparisons (gapSort p h.val) (g::w):ℝ))
        ≤ (2:ℝ)^167*(a+d) := by simpa only [tailMean,runWord_slots] using both
    apply (add_le_add first bt).trans
    nlinarith only [absorb,an,bn,dn]

#print axioms exists_continuation
end Shellsort.PrescribedTwoGapUpper
