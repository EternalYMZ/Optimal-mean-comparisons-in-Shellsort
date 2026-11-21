import Mathlib.Tactic.NormNum

/-! Closed numerical certificates, not a proof that the Fourier contraction
hypotheses hold. All inequalities are on natural numbers after clearing
positive denominators. D is 2^79 to allow the coarse 18 D^3 cutoff term. -/
namespace Shellsort.Actual214Calibration

theorem checked_budget :
    let D : ℕ := 2^79
    let m : ℕ := 324
    let J : ℕ := 2^15
    let R : ℕ := 2
    let A : ℕ := 2^260
    let B : ℕ := 2^16
    let near := (2*m-1)*128*R
    let far := 4*R*(R+2)*(2+D*D)
    (near*2^m+far*D)*2^61<D*2^m ∧
    (2*m-1)*(8*R*R*D+64*R)<2^15*D ∧
    18*D^3+J*2^15<2^243 ∧
    J*2^47≤2*2^61 ∧
    A*A*B*B+2^(47+242+1)*A*B ≤ 2^47*A*A ∧
    3^10<B ∧ 2*3^3<B ∧
    18800*4^9<(2:ℕ)^33 ∧ 18800*4^17<(2:ℕ)^49 ∧ 2*4^10*18800<(2:ℕ)^36 ∧
    3^7<(2:ℕ)^12 ∧ 4*A*B*2^12≤2^290 ∧
    (1+2^290)+33*(1+2^311)<(2:ℕ)^319 := by
  decide

end Shellsort.Actual214Calibration
