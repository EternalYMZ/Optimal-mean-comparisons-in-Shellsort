import Shellsort.StrictSuffixTransportLower
import Shellsort.ModularCut
import Shellsort.PredeterminedOptimum

/-! A sequence of gaps divisible by d, followed by a bounded legal finishing
suffix. All counters refer to ordinary linear insertion on the actual states. -/
noncomputable section
namespace Shellsort.ExceptionalGapLower
open HarvestBlockIteration

private theorem capped_distance {n H : ℕ} (p : RankPlacement n) (v : PositiveWord)
    (cap : ∀ g ∈ v, g.val ≤ H) :
    wordShiftDistance p v ≤ (H : ℝ) * ordinaryWordShifts p v := by
  induction v generalizing p with
  | nil => simp [ordinaryWordShifts, wordShiftDistance]
  | cons k ks ih =>
    have first : (k.val : ℝ) * gapInsertionCost p k.val k.property ≤
        (H : ℝ) * gapInsertionCost p k.val k.property := by
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (cap k (List.mem_cons_self ..))) (by positivity)
    have rest := ih (gapSort p k.val) (fun g hg => cap g (List.mem_cons_of_mem _ hg))
    simpa only [ordinaryWordShifts, wordShiftDistance, Nat.cast_add, mul_add] using add_le_add first rest

private theorem prefix_shifts {n : ℕ} (p : RankPlacement n) (u v : PositiveWord) :
    ordinaryWordShifts (sortWord p (u.map Subtype.val)) v ≤ ordinaryWordShifts p (u ++ v) := by
  induction u generalizing p with
  | nil => simp [sortWord]
  | cons k ks ih =>
    exact (ih (gapSort p k.val)).trans (Nat.le_add_left ..)

/-- Pointwise residual at the last divisible-only checkpoint, charged only
to successful right shifts in the suffix (not the prefix). -/
theorem exceptional_suffix {n d H : ℕ} (p : RankPlacement n) (u v : PositiveWord)
    (divs : ∀ k ∈ u, d ∣ k.val) (cap : ∀ k ∈ v, k.val ≤ H)
    (last : (v.map Subtype.val).getLast? = some 1) :
    footrule (gapSort p d) ≤
      (2*(H : ℝ)) * ordinaryWordShifts (sortWord p (u.map Subtype.val)) v := by
  let state := sortWord p (u.map Subtype.val)
  have at_cut : footrule (gapSort p d) ≤ footrule state :=
    divisible_word_footrule_lower p _ (by
      intro k h
      obtain ⟨k', hk', rfl⟩ := List.mem_map.mp h
      exact divs k' hk')
  have finish := footrule_le_wordShiftDistance state v
  rw [ComparisonAudit.sorted_last _ _ last] at finish
  have zero : footrule (Equiv.refl (Fin n)) = 0 := by simp [footrule, transport]
  rw [zero, zero_add] at finish
  have dist := capped_distance state v cap
  change _ ≤ (2*(H:ℝ)) * ordinaryWordShifts state v
  linarith only [at_cut, finish, dist]

/-- Any finite exception scale H imposes this lower bound on the mean
shifts, and therefore on the mean comparisons, of the *entire* fixed word.
Both bounds hold on a uniform permutation for every 2 ≤ d ≤ n. -/
theorem uniform_exception {n d H : ℕ} (hd : 2 ≤ d) (fits : d ≤ n)
    (u v : PositiveWord) (divs : ∀ k ∈ u, d ∣ k.val) (cap : ∀ k ∈ v, k.val ≤ H)
    (last : (v.map Subtype.val).getLast? = some 1) :
    let price := (n:ℝ) * Real.sqrt ((n:ℝ)*d) / 1024
    price ≤ (2*(H:ℝ)) * uniformAverage (fun p : RankPlacement n => (ordinaryWordShifts p (u++v):ℝ)) ∧
    price ≤ (2*(H:ℝ)) * uniformAverage (fun p : RankPlacement n => (ordinaryWordComparisons p (u++v):ℝ)) := by
  intro price
  have factor : 0 ≤ 2*(H:ℝ) := by positivity
  have point (p : RankPlacement n) : footrule (gapSort p d) ≤
      (2*(H:ℝ)) * ordinaryWordShifts p (u++v) :=
    (exceptional_suffix p u v divs cap last).trans
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (prefix_shifts p u v)) factor)
  have mean := uniformAverage_mono _ _ point
  rw [uniformAverage_const_mul] at mean
  have bound := (uniform_onePass_footrule_fluctuation_lower n d hd fits).trans mean
  refine ⟨bound, bound.trans (mul_le_mul_of_nonneg_left (uniformAverage_mono _ _ ?_) factor)⟩
  intro p
  exact Nat.cast_le.mpr ((le_max_left ..).trans (ordinaryWord_scan_bounds p (u++v)).1)

private theorem below_count {n : ℕ} (i : Fin n) :
    (∑ j : Fin n, if j < i then (1 : ℝ) else 0) = i.val := by
  have hset : Finset.univ.filter (fun j : Fin n => j < i) = Finset.Iio i := by ext; simp
  have cnt : (∑ j : Fin n, if j < i then (1 : ℕ) else 0) = i.val := by
    rw [← Finset.sum_filter, Finset.sum_const, hset, Fin.card_Iio]
    simp
  exact_mod_cast cnt

/-- Each slot of a 321-avoiding permutation is the left or the right
endpoint of its inversions. It cannot be both. -/
private theorem no_triple_footrule {n : ℕ} (q : Equiv.Perm (Fin n))
    (avoid : ∀ i j k, i < j → j < k → q j < q i → q k < q j → False) :
    (∑ v : Fin n, |(v.val : ℝ) - ((q v).val : ℝ)|) =
      2 * ∑ j : Fin n, ∑ i : Fin n, if i < j ∧ q j < q i then (1:ℝ) else 0 := by
  let inv (i j : Fin n) := if i < j ∧ q j < q i then (1:ℝ) else 0
  have endpoint (v : Fin n) : |(v.val : ℝ) - ((q v).val : ℝ)| =
      (∑ w : Fin n, inv w v) + ∑ w : Fin n, inv v w := by
    have signed : ((q v).val : ℝ) - (v.val : ℝ) =
        (∑ w : Fin n, inv v w) - ∑ w : Fin n, inv w v := by
      have perm := Equiv.sum_comp q (fun w : Fin n => if w < q v then (1:ℝ) else 0)
      rw [below_count] at perm
      rw [← perm, ← below_count v, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro w _
      rcases eq_or_ne w v with rfl | ne
      · simp [inv]
      · have diff : q w ≠ q v := fun e => ne (q.injective e)
        rcases lt_or_gt_of_ne ne with hw | hw <;> rcases lt_or_gt_of_ne diff with hq | hq <;>
          simp [inv, hw, hq, not_lt_of_gt hw, not_lt_of_gt hq]
    rw [abs_sub_comm, signed]
    have nonneg (i j) : 0 ≤ inv i j := by dsimp [inv]; split <;> norm_num
    by_cases left : ∃ w, w < v ∧ q v < q w
    · obtain ⟨u,hu,hq⟩ := left
      have right (w : Fin n) : inv v w = 0 := ite_eq_right fun h => avoid u v w hu h.1 hq h.2
      simp only [right, Finset.sum_const_zero, zero_sub, abs_neg, add_zero]
      exact abs_of_nonneg (Finset.sum_nonneg fun _ _ => nonneg _ _)
    · have empty (w : Fin n) : inv w v = 0 := ite_eq_right fun h => left ⟨w,h⟩
      simp only [empty, Finset.sum_const_zero, sub_zero, zero_add]
      exact abs_of_nonneg (Finset.sum_nonneg fun _ _ => nonneg _ _)
  calc
    _ = ∑ v : Fin n, ((∑ w : Fin n, inv w v) + ∑ w : Fin n, inv v w) :=
      Finset.sum_congr rfl fun v _ => endpoint v
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_comm (f := fun v w => inv v w)]
      change _ = 2 * ∑ v : Fin n, ∑ w : Fin n, inv w v
      ring

/-- After an ordinary gap-two pass the two parity chains increase. Thus
each inversion is counted twice by the global footrule, exactly. -/
theorem two_sorted_identity {n : ℕ} (p : RankPlacement n) :
    footrule (gapSort p 2) = 2 * (gapInversions (gapSort p 2) 1 : ℝ) := by
  let q := (gapSort p 2).symm
  have asc (i j : Fin n) (before : i < j) (same : i.val%2 = j.val%2) : q i < q j := by
    apply (gapSort_sorted p 2 (q i) (q j) (by simpa [q] using same)).mp
    simpa [q] using before
  have avoid (i j k : Fin n) (lt₁ : i < j) (lt₂ : j < k)
      (dec₁ : q j < q i) (dec₂ : q k < q j) : False := by
    have colors : i.val%2 = j.val%2 ∨ j.val%2 = k.val%2 ∨ i.val%2 = k.val%2 := by omega
    rcases colors with s | s | s
    · exact (not_lt_of_gt dec₁) (asc _ _ lt₁ s)
    · exact (not_lt_of_gt dec₂) (asc _ _ lt₂ s)
    · exact (not_lt_of_gt (dec₂.trans dec₁)) (asc _ _ (lt₁.trans lt₂) s)
  rw [footrule_by_positions, gapInversions_nat_pair_sum]
  push_cast
  simpa only [Nat.mod_one, and_true, Nat.cast_ite, Nat.cast_zero, Nat.cast_one]
    using no_triple_footrule q avoid

theorem parity_shift_price {n H : ℕ} (p : RankPlacement n) (u v : PositiveWord)
    (even : ∀ k ∈ u, 2 ∣ k.val) (cap : ∀ k ∈ v, k.val ≤ H)
    (last : (v.map Subtype.val).getLast? = some 1) :
    (gapInversions (gapSort p 2) 1 : ℝ) ≤
      H * (ordinaryWordShifts (sortWord p (u.map Subtype.val)) v : ℝ) := by
  have price := exceptional_suffix p u v even cap last
  rw [two_sorted_identity] at price
  linarith only [price]

private theorem split_word {d H : ℕ} (hp : 1 ≤ H) (w : PositiveWord)
    (order : (w.map Subtype.val).Pairwise (· > ·))
    (last : (w.map Subtype.val).getLast? = some 1)
    (exception : ∀ g ∈ w, H < g.val → d ∣ g.val) :
    ∃ u v : PositiveWord, w = u ++ v ∧ (∀ g ∈ u, d ∣ g.val) ∧
      (∀ g ∈ v, g.val ≤ H) ∧ (v.map Subtype.val).getLast? = some 1 := by
  induction w with
  | nil => simp at last
  | cons h tail ih =>
    obtain ⟨smaller, ord⟩ := List.pairwise_cons.mp order
    by_cases inside : h.val ≤ H
    · refine ⟨[], h::tail, rfl, by simp, ?_, last⟩
      intro g mem
      rcases List.mem_cons.mp mem with rfl | mem
      · exact inside
      · exact (smaller g.val (List.mem_map_of_mem mem)).le.trans inside
    · have tail_last : (tail.map Subtype.val).getLast? = some 1 := by
        cases tail with
        | nil => simp at last; omega
        | cons t ts => simpa only [List.map_cons, List.getLast?_cons_cons] using last
      obtain ⟨u,v,eq,divs,cap,finish⟩ := ih ord tail_last
        (fun g mem => exception g (List.mem_cons_of_mem _ mem))
      refine ⟨h::u, v, by rw [eq, List.cons_append], ?_, cap, finish⟩
      intro g mem
      rcases List.mem_cons.mp mem with rfl | mem
      · exact exception _ (List.mem_cons_self ..) (by omega)
      · exact divs _ mem

/-- On a legal Shellsort table the exceptional-gap cap itself determines
the cut. No separate prefix, suffix or number-of-passes assumption is needed. -/
theorem legal_exception {n d H : ℕ} (hd : 2 ≤ d) (fits : d ≤ n) (hp : 1 ≤ H)
    (w : PositiveWord) (legal : PredeterminedOptimum.Legal n w)
    (exception : ∀ g ∈ w, H < g.val → d ∣ g.val) :
    let price := (n:ℝ) * Real.sqrt ((n:ℝ)*d) / 1024
    price ≤ (2*(H:ℝ)) * uniformAverage (fun p : RankPlacement n => (ordinaryWordShifts p w:ℝ)) ∧
    price ≤ (2*(H:ℝ)) * uniformAverage (fun p : RankPlacement n => (ordinaryWordComparisons p w:ℝ)) := by
  obtain ⟨u,v,rfl,divs,cap,last⟩ := split_word hp w legal.1 legal.2.2 exception
  exact uniform_exception hd fits u v divs cap last

#print axioms exceptional_suffix
#print axioms uniform_exception
#print axioms two_sorted_identity
#print axioms parity_shift_price
#print axioms legal_exception

end Shellsort.ExceptionalGapLower
