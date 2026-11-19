module

public import Jsp000726.UpperInvariant

import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators

namespace Jsp000726.Upper

private theorem weighted_sum_eq_reference_and_error
    (A : Finset ℤ) (B g : ℤ) (row err weight : ℤ → ℤ)
    (ht : ∀ x ∈ A, x = B + g * row x + err x) :
    signedSum A weight =
      B * signedCard A weight + g * (∑ x ∈ A, weight x * row x) +
        (∑ x ∈ A, weight x * err x) := by
  unfold signedSum signedCard
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  calc
    weight x * x = weight x * (B + g * row x + err x) :=
      congrArg (fun y => weight x * y) (ht x hx)
    _ = _ := by ring

private theorem abs_weighted_sum_le (A : Finset ℤ) (err weight : ℤ → ℤ)
    (hw : ∀ x ∈ A, |weight x| ≤ 1) :
    |∑ x ∈ A, weight x * err x| ≤ ∑ x ∈ A, |err x| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro x hx
  rw [abs_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hw x hx) (abs_nonneg (err x))

/-- The old terms and the row fillers give a stronger invariant at the new modulus. -/
theorem invariant.refine_add_filler {A C : Finset ℤ} {B h d K : ℤ}
    (hi : invariant A B h d) (hB : 0 < B) (hd : 0 < d) (hK : d ∣ K)
    (hG : h ∣ B * K) (hAC : Disjoint A C) (row error : ℤ → ℤ)
    (hC : ∀ x ∈ C, x = B + B * K * row x + error x)
    (hError : ∀ x ∈ C, h ∣ error x)
    (hBudget : mass A B + (∑ x ∈ C, |error x|) < B * d) :
    invariant (A ∪ C) B (B * K) K := by
  have hres x (hx : x ∈ C) : h ∣ x - B := by
    rw [hC x hx]
    convert dvd_add (dvd_mul_of_dvd_left hG (row x)) (hError x hx) using 1; ring
  apply (hi.union_of_dvd_sub hAC hres).refine_modulus hB hd hK hG
  intro weight hw
  let i (x : ℤ) := if x ∈ A then 0 else row x
  let e (x : ℤ) := if x ∈ A then x - B else error x
  have hpoint x (hx : x ∈ A ∪ C) : x = B + B * K * i x + e x := by
    by_cases ha : x ∈ A
    · simp [i, e, ha]
    · have hc : x ∈ C := (Finset.mem_union.mp hx).resolve_left ha
      simpa [i, e, ha] using hC x hc
  have htotal : (∑ x ∈ A ∪ C, |e x|) = mass A B + (∑ x ∈ C, |error x|) := by
    rw [Finset.sum_union hAC]
    congr 1
    · unfold mass
      exact Finset.sum_congr rfl fun x hx => by simp [e, hx]
    · exact Finset.sum_congr rfl fun x hx => by
        have hx' : x ∉ A := fun ha => Finset.disjoint_left.mp hAC ha hx
        simp [e, hx']
  refine ⟨_, _, weighted_sum_eq_reference_and_error (A ∪ C) B (B * K) i e weight hpoint, ?_⟩
  apply (abs_weighted_sum_le (A ∪ C) e weight hw).trans_lt
  exact htotal ▸ hBudget

/-- The dense block then preserves the stronger invariant at the next reference. -/
theorem invariant.advance_stage {A C D : Finset ℤ} {B B' h d K : ℤ}
    (hi : invariant A B h d) (hB : 0 < B) (hd : 0 < d) (hK : d ∣ K)
    (hG : h ∣ B * K) (hAC : Disjoint A C) (hD : Disjoint (A ∪ C) D)
    (row error : ℤ → ℤ) (hC : ∀ x ∈ C, x = B + B * K * row x + error x)
    (hError : ∀ x ∈ C, h ∣ error x)
    (hBudget : mass A B + (∑ x ∈ C, |error x|) < B * d)
    (hDense : ∀ x ∈ D, B * K ∣ x - B) (hRef : B * K ∣ B' - B) :
    invariant ((A ∪ C) ∪ D) B' (B * K) K := by
  have hstep := invariant.refine_add_filler hi hB hd hK hG hAC row error hC hError hBudget
  exact invariant.change_reference (invariant.union_of_dvd_sub hstep hD hDense) hRef

/-- A multiple of `h / gcd(B,h)` makes the new step size divisible by `h`. -/
theorem dvd_step_of_period_dvd {B h K : ℕ} (hK : h / B.gcd h ∣ K) :
    h ∣ B * K := by
  obtain ⟨b, hb⟩ := Nat.gcd_dvd_left B h
  obtain ⟨k, rfl⟩ := hK
  refine ⟨b * k, ?_⟩
  calc
    B * (h / B.gcd h * k) = (B.gcd h * b) * (h / B.gcd h * k) := by rw [← hb]
    _ = (h / B.gcd h * B.gcd h) * (b * k) := by ac_rfl
    _ = h * (b * k) := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_right B h)]

/-- The period calculated from the new reference and modulus is exactly `K`. -/
theorem next_period_eq {B K R : ℕ} (hB : 0 < B) :
    B * K / (B + B * K * R).gcd (B * K) = K := by
  rw [Nat.gcd_add_mul_left_left, Nat.gcd_mul_right_right, Nat.mul_div_cancel_left _ hB]

end Jsp000726.Upper
