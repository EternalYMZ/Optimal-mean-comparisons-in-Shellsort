import Shellsort.RoughGapScaleAssembly

namespace Shellsort.RoughGapVariableScale

/-- Finite block induction for rounded geometric centres. `step` is a premise,
not a proof of the arithmetic/Fourier contraction for the Shellsort menu. -/
theorem invariant (levels : ℕ) (q H : ℕ → ℝ) (a k A B : ℝ)
    (ha : 0 ≤ a) (hk : 0 ≤ k) (hA : 0 ≤ A)
    (budget : a*(A*B)^2 + k*(A*B) ≤ A^2)
    (positive : ∀ i ≤ levels, 0 ≤ H i)
    (initial : q 0 ≤ (A * H 0)^2)
    (ratio : ∀ i < levels, H i ≤ B * H (i+1))
    (step : ∀ i < levels, q (i+1) ≤ a*q i + k*H (i+1)*Real.sqrt (q i)) :
    ∀ i ≤ levels, q i ≤ (A * H i)^2 := by
  intro i hi
  induction i with
  | zero => exact initial
  | succ i ih =>
    have il : i < levels := by omega
    have H0 := positive i il.le
    have H1 := positive (i+1) hi
    have old := ih il.le
    have compare : A * H i ≤ (A*B) * H (i+1) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (ratio i il) hA
    have sq := pow_le_pow_left₀ (mul_nonneg hA H0) compare 2
    have root : Real.sqrt (q i) ≤ A * H i := by
      simpa only [Real.sqrt_sq (mul_nonneg hA H0)] using Real.sqrt_le_sqrt old
    calc
      q (i+1) ≤ _ := step i il
      _ ≤ a*((A*B)*H (i+1))^2 + k*H (i+1)*((A*B)*H (i+1)) :=
        add_le_add (mul_le_mul_of_nonneg_left (old.trans sq) ha)
          (mul_le_mul_of_nonneg_left (root.trans compare) (mul_nonneg hk H1))
      _ = (a*(A*B)^2+k*(A*B))*(H (i+1))^2 := by ring
      _ ≤ A^2*(H (i+1))^2 := mul_le_mul_of_nonneg_right budget (sq_nonneg _)
      _ = _ := by ring

#print axioms invariant
end Shellsort.RoughGapVariableScale
