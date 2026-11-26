import Mathlib.Algebra.GCDMonoid.Finset
import Shellsort.ConsecutiveMenus

/-! Finite arithmetic for eventually periodic gap catalogues. -/
namespace Shellsort.PeriodicMenus
open Finset

def anchors (c q a₀ : ℕ) (A : Finset ℕ) : Finset ℕ :=
  insert (3*c+a₀+q) (A.image fun a => 3*c+a)

/-- The offset anchor recovers q by subtraction. At every aligned scale
the gcd of the full anchor family is exactly the gcd of q and the residues. -/
theorem anchors_gcd {c q a₀ : ℕ} {A : Finset ℕ} (aligned : q ∣ c) (member : a₀ ∈ A) :
    (anchors c q a₀ A).gcd id = (insert q A).gcd id := by
  have equiv (d : ℕ) : d ∣ (anchors c q a₀ A).gcd id ↔ d ∣ (insert q A).gcd id := by
    simp only [anchors, Finset.dvd_gcd_iff, forall_mem_insert, forall_mem_image, id_eq]
    constructor
    · rintro ⟨top, all⟩
      have dq := (Nat.dvd_add_iff_right (all member)).mpr top
      have dc : d ∣ 3*c := dvd_mul_of_dvd_right (dq.trans aligned) 3
      exact ⟨dq, fun a ha => (Nat.dvd_add_iff_right dc).mpr (all ha)⟩
    · rintro ⟨dq, all⟩
      have dc : d ∣ 3*c := dvd_mul_of_dvd_right (dq.trans aligned) 3
      exact ⟨dvd_add (dvd_add dc (all a₀ member)) dq, fun a ha => dvd_add dc (all a ha)⟩
  exact Nat.dvd_antisymm ((equiv _).mp dvd_rfl) ((equiv _).mpr dvd_rfl)

def menu (c q : ℕ) (A : Finset ℕ) :=
  (Ico c (2*c)).filter fun h => h % q ∈ A

/-- Quotient and remainder identify the menu with k complete residue periods. -/
theorem menu_card (q k : ℕ) (A : Finset ℕ) (qp : 0 < q) (res : ∀ a ∈ A, a < q) :
    (menu (k*q) q A).card = k * A.card := by
  let P := (Ico k (2*k)) ×ˢ A
  have decode (i a : ℕ) (small : a < q) :
      (q*i+a)/q = i ∧ (q*i+a)%q = a := by
    simp [Nat.mul_add_div qp, Nat.div_eq_of_lt small, Nat.mod_eq_of_lt small]
  have bounds (h : ℕ) : h ∈ Ico (k*q) (2*(k*q)) ↔ h / q ∈ Ico k (2*k) := by
    simp only [mem_Ico, Nat.le_div_iff_mul_le qp, Nat.div_lt_iff_lt_mul qp, Nat.mul_assoc]
  calc
    _ = P.card := by
      apply card_bij (fun h _ => (h / q, h % q))
      · intro h hh
        exact mem_product.mpr ⟨(bounds h).mp (mem_filter.mp hh).1, (mem_filter.mp hh).2⟩
      · intro x _ y _ eq
        have eq₁ : x/q = y/q := congrArg Prod.fst eq
        have eq₂ : x%q = y%q := congrArg Prod.snd eq
        calc
          x = q*(x/q) + x%q := (Nat.div_add_mod _ _).symm
          _ = q*(y/q) + y%q := by rw [eq₁, eq₂]
          _ = y := Nat.div_add_mod _ _
      · rintro ⟨i,a⟩ mem
        obtain ⟨hi, ha⟩ := mem_product.mp mem
        obtain ⟨iq, ar⟩ := decode i a (res a ha)
        refine ⟨q*i+a, mem_filter.mpr ⟨(bounds _).mpr ?_, ?_⟩, Prod.ext iq ar⟩
        · rw [iq]; exact hi
        · rw [ar]; exact ha
    _ = _ := by simp [P, Nat.card_Ico]; omega

def residues210 : Finset ℕ := {30, 42, 70, 105}

/-- All four residues together have gcd one with q, although each triple
of residues, including repetitions, has a common divisor with q above one. -/
theorem four_residues :
    (insert 210 residues210).gcd id = 1 ∧
      ∀ x ∈ residues210, ∀ y ∈ residues210, ∀ z ∈ residues210,
        1 < Nat.gcd 210 (Nat.gcd x (Nat.gcd y z)) := by decide

/-- The three-gap obstruction holds for actual gap values of arbitrary
size in the periodic catalogue, including repeated residues. -/
theorem every_three_share_prime (x y z : ℕ) (hx : x%210 ∈ residues210)
    (hy : y%210 ∈ residues210) (hz : z%210 ∈ residues210) :
    ∃ p : ℕ, p.Prime ∧ p ∣ 210 ∧ p ∣ x ∧ p ∣ y ∧ p ∣ z := by
  let D := (210 : ℕ).gcd ((x%210).gcd ((y%210).gcd (z%210)))
  have gt : 1 < D := four_residues.2 _ hx _ hy _ hz
  let p := D.minFac
  have prime : p.Prime := Nat.minFac_prime (by omega : D ≠ 1)
  have pd : p ∣ D := Nat.minFac_dvd D
  have pq := pd.trans (Nat.gcd_dvd_left _ _)
  have px_yz := pd.trans (Nat.gcd_dvd_right _ _)
  have pyz := px_yz.trans (Nat.gcd_dvd_right _ _)
  have lift (s : ℕ) (divides : p ∣ s%210) : p ∣ s := by
    rw [← Nat.div_add_mod s 210]
    exact dvd_add (dvd_mul_of_dvd_left pq _) divides
  exact ⟨p, prime, pq, lift x (px_yz.trans (Nat.gcd_dvd_left _ _)),
    lift y (pyz.trans (Nat.gcd_dvd_left _ _)), lift z (pyz.trans (Nat.gcd_dvd_right _ _))⟩

#print axioms anchors_gcd
#print axioms menu_card
#print axioms four_residues
#print axioms every_three_share_prime

end Shellsort.PeriodicMenus
