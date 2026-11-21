import Shellsort.FirstPassUpper
import Shellsort.RoughGapPredeterminedSelection

/-! Mean squared displacement of the actual state after the prescribed first gap. -/
noncomputable section
namespace Shellsort.FirstGapMeanEnergy
open Finset

theorem tag_square_bound {n : ℕ} (h : ℕ) (hh : 0<h) (i : Fin n) :
    uniformAverage (fun p : RankPlacement n =>
      (((gapSort p h (p.symm i)).val:ℝ) - ((p.symm i).val:ℝ))^2) ≤
      ((h:ℝ)-1)^2 + (n:ℝ)*h/4 := by
  simp_rw [actual_onePass_tag_displacement _ h hh i]
  apply uniform_tagged_mean_le_of_full_bernoulli_bound i
    (fun B => (firstPassSubsetDisplacement h i B.val)^2)
  intro t lo hi
  change mean (bernoulliVectorWeight t n)
    (fun z => (firstPassSubsetDisplacement h i (fullBitsSubset i z))^2) ≤ _
  simp_rw [fullBits_onePass_displacement]
  change secondMoment (bernoulliVectorWeight t n) (firstPassBitDisplacement h i) ≤ _
  have identity := centeredSecond_identity (bernoulliVectorWeight t n)
    (firstPassBitDisplacement h i) (bernoulliVectorWeight_sum t n)
  have variance := firstPassBitDisplacement_variance_bound h hh i t
  have absmean := firstPassBitDisplacement_mean_bound h hh i t ⟨lo,hi⟩
  have squared := pow_le_pow_left₀ (abs_nonneg _) absmean 2
  rw [sq_abs] at squared
  linarith

private theorem physical_square {n : ℕ} (p : RankPlacement n) (h : ℕ) :
    (RoughGapScaleAssembly.squareDisplacement (gapSort p h):ℝ) =
      ∑ i : Fin n, (((gapSort p h (p.symm i)).val:ℝ)-((p.symm i).val:ℝ))^2 := by
  simp only [RoughGapScaleAssembly.squareDisplacement, Int.cast_sum, Int.cast_pow,
    Int.cast_sub, Int.cast_natCast]
  exact (p.symm.sum_comp (fun x => (((gapSort p h x).val:ℝ) - (x.val:ℝ))^2)).symm

theorem first_gap_energy_finite {n h : ℕ} (hh : 0<h) (hn : 0<n) :
    uniformAverage (fun p : RankPlacement n => RoughGapSelection.energy (gapSort p h)) ≤
      ((h:ℝ)-1)^2 + (n:ℝ)*h/4 := by
  have avg : uniformAverage (fun p : RankPlacement n =>
      (RoughGapScaleAssembly.squareDisplacement (gapSort p h):ℝ)) =
      ∑ i : Fin n, uniformAverage (fun p : RankPlacement n =>
        (((gapSort p h (p.symm i)).val:ℝ)-((p.symm i).val:ℝ))^2) := by
    simp_rw [physical_square]
    unfold uniformAverage
    rw [sum_comm,sum_div]
  have bound := Finset.sum_le_sum (s:= univ) (fun (i : Fin n) _ => tag_square_bound h hh i)
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at bound
  unfold RoughGapSelection.energy
  simp_rw [div_eq_inv_mul]
  rw [uniformAverage_const_mul,avg,←div_eq_inv_mul]
  exact (div_le_iff₀ (show (0:ℝ)<n by exact_mod_cast hn)).mpr (by linarith)

/-- Directly in the energy used by the real menu, uniformly in h and n. -/
theorem first_gap_energy_upper {n h : ℕ} (hh : 0<h) (fits : h≤n) :
    uniformAverage (fun p : RankPlacement n => RoughGapSelection.energy (gapSort p h)) ≤
      (2:ℝ)*n*h := by
  apply (first_gap_energy_finite hh (hh.trans_le fits)).trans
  have one : (1:ℝ) ≤ h := by exact_mod_cast hh
  have capped : (h:ℝ) ≤ n := by exact_mod_cast fits
  nlinarith [mul_le_mul_of_nonneg_right capped (Nat.cast_nonneg h : (0:ℝ)≤h)]

#print axioms first_gap_energy_upper
end Shellsort.FirstGapMeanEnergy
