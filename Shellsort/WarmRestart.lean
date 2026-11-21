import Shellsort.HarvestChosenLower
import Shellsort.HarvestTenCover

/-! Start the menu at an externally imposed gap cap.  The excess over the
steady scale loses one half at each actual choice, so its total cost is paid
once. The input size and the initial menu scale are separate parameters. -/
noncomputable section
namespace Shellsort.WarmRestart
open Actual214 HarvestBlockIteration HarvestTenSchedule HarvestTenCover
open HarvestMenuBlock HarvestScaleNumbers

private def base : ℝ := 2^115
private def extra : ℝ := 2^57
private def rate : ℝ := 1+2^165

private theorem contract {x z : ℝ} {H c : ℕ} (hz : 0 ≤ z)
    (entry : x ≤ ((base+z)*H)^2) (ratio : H ≤ 2^16*c) :
    (1/(2:ℝ)^47)*x+(2:ℝ)^98*c*Real.sqrt x ≤ ((base+z/2)*c)^2 := by
  have ratio' : (H:ℝ) ≤ (2:ℝ)^16*c := by exact_mod_cast ratio
  have bz : 0≤base+z := add_nonneg (by norm_num [base]) hz
  have q := entry.trans (pow_le_pow_left₀ (mul_nonneg bz (Nat.cast_nonneg _))
    (mul_le_mul_of_nonneg_left ratio' bz) 2)
  have rt := (Real.sqrt_le_sqrt q).trans_eq (Real.sqrt_sq (by positivity))
  have poly : (1/(2:ℝ)^47)*((base+z)*2^16)^2+2^98*((base+z)*2^16) ≤ (base+z/2)^2 := by
    norm_num [base] at *
    nlinarith only [sq_nonneg z,hz]
  calc
    _ ≤ (1/(2:ℝ)^47)*((base+z)*(2^16*c))^2+(2:ℝ)^98*c*((base+z)*(2^16*c)) := by gcongr
    _ = ((1/(2:ℝ)^47)*((base+z)*2^16)^2+2^98*((base+z)*2^16))*(c:ℝ)^2 := by ring
    _ ≤ (base+z/2)^2*(c:ℝ)^2 := mul_le_mul_of_nonneg_right poly (sq_nonneg _)
    _ = _ := by ring

private def Warm {n : ℕ} (P : RankPlacement n → RankPlacement n)
    (H : ℕ) (z : ℝ) : List Stage → List ℕ → Prop
  | [], [] => meanEnergy P ≤ ((base+z)*H)^2
  | s::ss, a::as => meanEnergy P ≤ ((base+z)*H)^2 ∧ a∈choices s.j ∧
      Warm (fun p => sortWord (P p) (stageWord s a)) (gap s.j) (z/2) ss as
  | _,_ => False

private theorem select_warm {n H : ℕ} (hn : 0<n) (P : RankPlacement n → RankPlacement n)
    (ss : List Stage) (fit : Centers H ss) (z : ℝ) (hz : 0≤z)
    (entry : meanEnergy P ≤ ((base+z)*H)^2) : ∃ as, Warm P H z ss as := by
  induction ss generalizing P H z with
  | nil => exact ⟨[],entry⟩
  | cons s ss ih =>
    obtain ⟨large,ratio,rest⟩ := fit
    obtain ⟨a,mem,budget⟩ := select_actual_linear_block hn P s.j large
    have core := budget.trans (contract hz entry ratio)
    have post := (word_mean_le (fun p => block s.j a (P p)) s.suffix).trans core
    have next : meanEnergy (fun p => sortWord (P p) (stageWord s a)) ≤
        ((base+z/2)*gap s.j)^2 := by
      simp only [stageWord,sortWord]
      exact post
    obtain ⟨as,ha⟩ := ih (H:=gap s.j) (fun p => sortWord (P p) (stageWord s a))
      rest (z/2) (div_nonneg hz (by norm_num)) next
    exact ⟨a::as,entry,mem,ha⟩

private theorem choices_of_warm {n H : ℕ} {P : RankPlacement n → RankPlacement n}
    {z : ℝ} {ss : List Stage} {as : List ℕ} (warm : Warm P H z ss as) :
    List.Forall₂ (fun s a => a∈choices s.j) ss as := by
  induction ss generalizing as H z P with
  | nil => cases as with
    | nil => exact .nil
    | cons => exact False.elim warm
  | cons s ss ih => cases as with
    | nil => exact False.elim warm
    | cons a as => exact .cons warm.2.1 (ih warm.2.2)

private theorem pay_local {n H m : ℕ} (hn : 0<n) (hm : 0<m)
    (P : RankPlacement n → RankPlacement n) (w : PositiveWord)
    (lo : ∀ g ∈ w, m ≤ g.val) (rat : H ≤ 2^49*m) (short : w.length ≤ 33)
    (z : ℝ) (hz : 0≤z) (entry : meanEnergy P ≤ ((base+z)*H)^2) :
    uniformAverage (fun p => (ordinaryWordComparisons (P p) w:ℝ)) ≤
      (w.length:ℝ)*(rate*n) + (extra/2)*z*n := by
  have bz : 0≤base+z := add_nonneg (by norm_num [base]) hz
  have rat' : (H:ℝ) ≤ (2:ℝ)^49*m := by exact_mod_cast rat
  have e : meanEnergy P ≤ (((base+z)*2^49)*m)^2 := by
    rw [mul_assoc]
    exact entry.trans (pow_le_pow_left₀ (mul_nonneg bz (Nat.cast_nonneg _))
      (mul_le_mul_of_nonneg_left rat' bz) 2)
  apply (HarvestWordCost.actual_word_from_square hn hm P w lo ((base+z)*2^49)
    (by positivity) e).trans
  have len : (w.length:ℝ) ≤ 33 := by exact_mod_cast short
  have debt : (w.length:ℝ)*(2:ℝ)^50 ≤ extra/2 := by
    exact (mul_le_mul_of_nonneg_right len (by positivity)).trans (by norm_num [extra])
  have coef : 1+2*((base+z)*2^49) = rate+2^50*z := by unfold base rate; ring
  rw [coef]
  calc
    _ = (w.length:ℝ)*(rate*n) + ((w.length:ℝ)*2^50)*z*n := by ring
    _ ≤ _ := by gcongr

private theorem short_stages (k : ℕ) : ∀ s ∈ stages k, s.suffix.length ≤ 7 := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [stages_eq]
    split
    · rename_i ok
      intro s h
      rcases List.mem_cons.mp h with rfl | mem
      · simp [chunk]
      · exact ih (k-10) (by have := ok.1; omega) s mem
    · simp

private theorem pay_all {n : ℕ} (hn : 0<n) (ss : List Stage) (as : List ℕ)
    (ws : List PositiveWord) (tail : PositiveWord) (tailshort : tail.length ≤ 33)
    (P : RankPlacement n → RankPlacement n) (H : ℕ) (z : ℝ) (hz : 0≤z)
    (warm : Warm P H z ss as) (covers : Covers (2^28) H ss as ws)
    (end_small : endCenter H ss ≤ 2^49) (short : ∀ s ∈ ss, s.suffix.length ≤ 7) :
    uniformAverage (fun p => (ordinaryWordComparisons (P p) (ws.flatten++tail):ℝ)) ≤
      ((ws.flatten++tail).length:ℝ)*(rate*n) + extra*z*n := by
  induction ss generalizing as ws P H z with
  | nil =>
    cases as with
    | cons => exact False.elim warm
    | nil =>
      cases ws with
      | cons => exact False.elim covers
      | nil =>
        have b := pay_local hn (by decide : 0<1) P tail (fun g _ => g.property)
          (show H ≤ 2^49*1 by simpa [endCenter] using end_small) tailshort z hz warm
        apply b.trans
        change (tail.length:ℝ)*(rate*n)+(extra/2)*z*n ≤ (tail.length:ℝ)*(rate*n)+extra*z*n
        gcongr
        norm_num [extra]
  | cons s ss ih =>
    cases as with
    | nil => exact False.elim warm
    | cons a as =>
      cases ws with
      | nil => exact False.elim covers
      | cons w ws =>
        obtain ⟨agree,⟨m,hm,rat,lo⟩,cover'⟩ := covers
        have len := congrArg List.length agree
        simp only [List.length_map,stageWord,List.length_cons] at len
        have shortw : w.length ≤ 33 := by have := short s List.mem_cons_self; omega
        have rat' : H ≤ 2^49 * m := rat.trans (Nat.mul_le_mul_right m (by decide))
        have pay := pay_local hn hm P w lo rat' shortw z hz warm.1
        have rest := ih as ws (fun p => sortWord (P p) (stageWord s a)) (gap s.j)
          (z/2) (by positivity) warm.2.2 cover' end_small
          (fun t ht => short t (List.mem_cons_of_mem _ ht))
        simp only [List.flatten_cons,List.append_assoc,comparisons_append,
          Nat.cast_add,uniformAverage_add,agree,List.length_append] at pay rest ⊢
        calc
          _ ≤ _ := add_le_add pay rest
          _ = _ := by ring

private theorem last_sorts {n : ℕ} (w : List ℕ) (p : RankPlacement n)
    (h : w.getLast? = some 1) : sortWord p w = Equiv.refl _ := by
  induction w generalizing p with
  | nil => simp at h
  | cons a as ih =>
    cases as with
    | nil =>
      have eq : a=1 := by simpa using h
      subst a
      exact gapSort_one p
    | cons b bs =>
      have last : (b::bs).getLast?=some 1 := h
      change sortWord (gapSort p a) (b::bs) = _
      exact ih (gapSort p a) last

/-- For any fixed source map P on n positions, start the schedule using the
external scale H. Its post-checkpoint comparison cost has one additive term
proportional to the incoming root-mean-square displacement divided by H. -/
theorem exists_strict_suffix {n H : ℕ} (hn : 0<n) (hH : 2≤H)
    (P : RankPlacement n → RankPlacement n) :
    ∃ w : PositiveWord,
      (w.map Subtype.val).Pairwise (· > ·) ∧ (∀ g ∈ w, 2*g.val ≤ H) ∧
      (H::w.map Subtype.val).Pairwise (· > ·) ∧
      (w.map Subtype.val).getLast? = some 1 ∧
      (∀ q : RankPlacement n, sortWord q (w.map Subtype.val) = Equiv.refl _) ∧
      w.length ≤ Nat.log 2 H ∧
      uniformAverage (fun p => (ordinaryWordComparisons (P p) w:ℝ)) ≤
        (1+(2:ℝ)^165)*n*Real.logb 2 H+
        (2:ℝ)^57*(Real.sqrt (meanEnergy P)/(H:ℝ))*n := by
  let z := Real.sqrt (meanEnergy P)/(H:ℝ)
  have hp : (0:ℝ)<H := by exact_mod_cast (show 0<H by omega)
  have hz : 0≤z := div_nonneg (Real.sqrt_nonneg _) hp.le
  have ini : meanEnergy P ≤ ((base+z)*H)^2 := by
    have a : Real.sqrt (meanEnergy P) ≤ (base+z)*H := by
      rw [add_mul,show z*(H:ℝ)=Real.sqrt (meanEnergy P) by dsimp [z]; field_simp]
      exact le_add_of_nonneg_left (mul_nonneg (by norm_num [base]) hp.le)
    by_cases e : 0≤meanEnergy P
    · calc
        _ = Real.sqrt (meanEnergy P)^2 := (Real.sq_sqrt e).symm
        _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) a 2
    · exact (lt_of_not_ge e).le.trans (sq_nonneg _)
  let k := count H
  let ss := stages k
  have fit : Centers H ss := centers_from_size hH
  obtain ⟨as,warm⟩ := select_warm hn P ss fit z hz ini
  have picks := choices_of_warm warm
  obtain ⟨ws,covers⟩ := menu_covers fit picks
  let t := positiveTail (tailCount k)
  let w := ws.flatten++t
  have pay := pay_all hn ss as ws t (by simpa [t] using tail_count_bound k)
    P H z hz warm covers (end_center_bound hH) (short_stages k)
  have word : w.map Subtype.val = realizedWord ss as ++ tailWord k := by
    simp only [w,t,List.map_append,covers_word covers]
    congr 1
    exact positiveTail_values _
  have len : w.length = k := by simpa [w,t] using covers_length covers
  have lnat : w.length ≤ Nat.log 2 H := len.le.trans (count_le_log hH)
  have legal := HarvestTenLegal.full_word_legal hH as picks
  have half (g) (hg : g∈w) : 2*g.val ≤ H := by
    have mem : g.val ∈ w.map Subtype.val := List.mem_map_of_mem hg
    exact HarvestChosenLower.chosen_gap_half hH as picks g.val (word ▸ mem)
  have dec : (w.map Subtype.val).Pairwise (· > ·) := word ▸ legal.1
  have last : (w.map Subtype.val).getLast? = some 1 := word ▸ legal.2.2
  refine ⟨w,dec,half,List.pairwise_cons.mpr ⟨?_,dec⟩,last,fun q => last_sorts _ q last,lnat,?_⟩
  · intro v hv
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hv
    have := half g hg
    have := g.property
    omega
  · have logBound := (show (w.length:ℝ) ≤ (Nat.log 2 H:ℝ) by exact_mod_cast lnat).trans
        (Real.natLog_le_logb H 2)
    apply pay.trans
    change (w.length:ℝ)*(rate*n)+extra*z*n ≤ rate*n*Real.logb 2 H + extra*z*n
    rw [mul_comm (w.length:ℝ)]
    have pos : 0 ≤ rate * (n:ℝ) := mul_nonneg (by norm_num [rate]) (Nat.cast_nonneg _)
    exact add_le_add (mul_le_mul_of_nonneg_left logBound pos) le_rfl

#print axioms exists_strict_suffix
end Shellsort.WarmRestart
