import Shellsort.GapSuffixEntropy
import Shellsort.StrictSuffixTransportLower
import Shellsort.PrescribedFirstGapTailUpper

/-! Uniform lower and upper bounds on the comparisons executed strictly
after the prescribed first pass. -/
noncomputable section
namespace Shellsort.PrescribedFirstGapTailMatching
open Finset HarvestBlockIteration HarvestOperationalAudit

private theorem log_scale {y : ℝ} (hy : 1≤y) :
    Real.logb 2 (2*y) ≤ 5*Real.sqrt y := by
  have yp : 0<y := by linarith
  have sy : 1≤Real.sqrt y := by simpa using Real.sqrt_le_sqrt hy
  have half := Real.log_le_sub_one_of_pos (show (0:ℝ)<(2:ℝ)⁻¹ by norm_num)
  rw [Real.log_inv] at half
  have ltwo : (1:ℝ)/2 ≤ Real.log 2 := by linarith
  have lin := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr yp)
  rw [Real.log_sqrt yp.le] at lin
  unfold Real.logb
  rw [Real.log_mul (by norm_num) yp.ne']
  apply (div_le_iff₀ (Real.log_pos (show (1:ℝ)<2 by norm_num))).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr sy) (sub_nonneg.mpr ltwo)]

private theorem fiber_logs {n H : ℕ} (hh : 0<H) (fits : H≤n) :
    (∑ s : Fin H, Real.logb 2 ((residuePrefixCount H s.val n).factorial:ℝ)) ≤
      (n:ℝ)*Real.logb 2 (2*((n:ℝ)/H)) := by
  let m := fun s : Fin H => residuePrefixCount H s.val n
  let y := (n:ℝ)/H
  have hp : (0:ℝ)<H := by exact_mod_cast hh
  have hy : 1≤y := (one_le_div hp).2 (by exact_mod_cast fits)
  have sumN : ∑ s : Fin H, m s = n := by
    calc
      _ = ∑ s : Fin H, sourceTrialLength (n/H) (n%H) s.val := by
        apply sum_congr rfl
        intro s _
        exact (chainPositions_card n H s.val).symm.trans (actual_chain_length n H hh s)
      _ = _ := sum_actual_chain_lengths n H hh
  have sumR : ∑ s : Fin H, (m s:ℝ) = n := by exact_mod_cast sumN
  have localBound (s : Fin H) : Real.logb 2 ((m s).factorial:ℝ) ≤ (m s:ℝ)*Real.logb 2 (2*y) := by
    have q : ((n/H:ℕ):ℝ) ≤ y := by
      apply (le_div_iff₀ hp).mpr
      exact_mod_cast Nat.div_mul_le_self n H
    have mm : (m s:ℝ) ≤ 2*y := by
      have term : m s ≤ n/H+1 := by
        dsimp [m]
        rw [residuePrefixCount_formula H s.val n hh s.isLt]
        split <;> omega
      have termR : (m s:ℝ) ≤ ((n/H:ℕ):ℝ)+1 := by exact_mod_cast term
      linarith
    have fak : ((m s).factorial:ℝ) ≤ (2*y)^(m s) := by
      calc
        _ ≤ (m s:ℝ)^(m s) := by exact_mod_cast Nat.factorial_le_pow (m s)
        _ ≤ _ := pow_le_pow_left₀ (Nat.cast_nonneg _) mm _
    simpa only [Real.logb_pow] using Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
      (by positivity : (0:ℝ)<(m s).factorial) fak
  calc
    _ ≤ ∑ s : Fin H, (m s:ℝ)*Real.logb 2 (2*y) := sum_le_sum fun s _ => localBound s
    _ = _ := by rw [←sum_mul,sumR]

def tailMean (n H : ℕ) (v : PositiveWord) : ℝ :=
  uniformAverage fun p : RankPlacement n => ((runWord (slots (gapSort p H)) v).2:ℝ)

theorem uniform_lower {n H : ℕ} (hH : 2≤H) (fits : H≤n) (v : PositiveWord)
    (cap : ∀ g∈v, g.val≤H) (last : (v.map Subtype.val).getLast?=some 1) :
    (n:ℝ)*Real.logb 2 n+(n:ℝ)*Real.sqrt ((n:ℝ)/H) ≤ 32768*tailMean n H v := by
  let cost := tailMean n H v
  have hp : (0:ℝ)<H := by exact_mod_cast (by omega : 0<H)
  have hy : 1≤(n:ℝ)/H := (one_le_div hp).2 (by exact_mod_cast fits)
  have entropy := GapSuffixEntropy.mean_suffix_entropy (n:=n) (h:=H) (by omega) v last
  have travel := StrictSuffixTransportLower.suffix_fluctuation_lower hH fits v cap last
  have eqn : uniformAverage (fun p : RankPlacement n =>
      (ordinaryWordComparisons (gapSort p H) v:ℝ)) = cost := by simp [cost,tailMean,runWord_slots]
  rw [eqn] at entropy travel
  have a := ComparisonTranscriptBound.half_nlog_le_log_factorial (n:=n) (by omega)
  have b := fiber_logs (n:=n) (H:=H) (by omega) fits
  have c := mul_le_mul_of_nonneg_left (log_scale hy) (Nat.cast_nonneg n : (0:ℝ)≤n)
  have p : 0≤cost := by
    apply le_trans _ travel
    positivity
  change _ ≤ 32768*cost
  nlinarith only [travel,entropy,a,b,c,p]

theorem matching_bounds {n H : ℕ} (hH : 2≤H) (hN : H<n) :
    let target := (n:ℝ)*Real.logb 2 n + (n:ℝ)*Real.sqrt ((n:ℝ)/H)
    (∀ v : PositiveWord, (∀ g∈v, g.val≤H) → (v.map Subtype.val).getLast?=some 1 →
      target ≤ 32768*tailMean n H v) ∧
    ∃ w : PositiveWord, (H::w.map Subtype.val).Pairwise (· > ·) ∧
      (w.map Subtype.val).getLast?=some 1 ∧ w.length≤Nat.log 2 H ∧
      (∀ p : RankPlacement n, (runWord (slots (gapSort p H)) w).1=Vector.ofFn id) ∧
      tailMean n H w ≤ (2:ℝ)^166*target := by
  constructor
  · exact uniform_lower hH hN.le
  obtain ⟨w,order,last,len,sorted,pay⟩ := PrescribedFirstGapTailUpper.exists_tail hH hN
  refine ⟨w,order,last,len,sorted,?_⟩
  apply pay.trans
  have hlog : Real.logb 2 H ≤ Real.logb 2 n :=
    Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast (by omega : 0<H)) (by exact_mod_cast hN.le)
  have mul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg n : (0:ℝ)≤n)
  have l : 0≤(n:ℝ)*Real.logb 2 n := by
    apply mul_nonneg (Nat.cast_nonneg _)
    exact Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1≤n))
  have r : 0≤(n:ℝ)*Real.sqrt ((n:ℝ)/H) := by positivity
  nlinarith only [mul,l,r]

#print axioms matching_bounds
end Shellsort.PrescribedFirstGapTailMatching
