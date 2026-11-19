module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Abs

import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators

namespace Jsp000726.Upper

/-- The signed sum obtained by assigning each element of a finite set an integer weight. -/
def signedSum (A : Finset ℤ) (weight : ℤ → ℤ) : ℤ :=
  ∑ x ∈ A, weight x * x

/-- The difference in the sizes of the positive- and negative-weight supports. -/
def signedCard (A : Finset ℤ) (weight : ℤ → ℤ) : ℤ :=
  ∑ x ∈ A, weight x

/-- The sum of the distances of the terms from the reference value. -/
def mass (A : Finset ℤ) (B : ℤ) : ℤ :=
  ∑ x ∈ A, |x - B|

/-- The old, near-reference terms retain their signed cardinality modulo a period. -/
def invariant (A : Finset ℤ) (B h d : ℤ) : Prop :=
  ∀ (weight : ℤ → ℤ), (∀ x ∈ A, |weight x| ≤ 1) → ∀ q : ℤ,
    h ∣ signedSum A weight + B * q → d ∣ signedCard A weight + q

private theorem eq_zero_of_dvd_of_abs_lt {m x : ℤ} (hm : 0 < m)
    (h : m ∣ x) (hx : |x| < m) : x = 0 := by
  obtain ⟨k, rfl⟩ := h
  by_cases hk : k = 0
  · simp [hk]
  · have hk' : 1 ≤ |k| := by
      have h' : |k| ≠ 0 := abs_ne_zero.mpr hk
      have hn := abs_nonneg k
      omega
    rw [abs_mul, abs_of_pos hm] at hx
    have hc : m * 1 ≤ m * |k| := mul_le_mul_of_nonneg_left hk' hm.le
    rw [mul_one] at hc
    omega

private theorem abs_signed_deviation_le_sum_abs (A : Finset ℤ) (B : ℤ)
    (weight : ℤ → ℤ) (hw : ∀ x ∈ A, |weight x| ≤ 1) :
    |signedSum A weight - B * signedCard A weight| ≤ mass A B := by
  have heq :
      signedSum A weight - B * signedCard A weight =
        ∑ x ∈ A, weight x * (x - B) := by
    unfold signedSum signedCard
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [heq]
  unfold mass
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro x hx
  rw [abs_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hw x hx) (abs_nonneg (x - B))

/-- The deviation budget turns the modular cardinality invariant into exact admissibility. -/
theorem invariant.signedCard_eq_zero {A : Finset ℤ} {B h d : ℤ}
    (hi : invariant A B h d) (hB : 0 < B) (hd : 0 < d) (hm : mass A B < B * d)
    (weight : ℤ → ℤ) (hw : ∀ x ∈ A, |weight x| ≤ 1)
    (hs : signedSum A weight = 0) : signedCard A weight = 0 := by
  have hdvd : d ∣ signedCard A weight := by
    simpa only [add_zero] using hi weight hw 0 (by simp [hs])
  obtain ⟨k, hk⟩ := hdvd
  have hb : |signedSum A weight - B * signedCard A weight| < B * d :=
    (abs_signed_deviation_le_sum_abs A B weight hw).trans_lt hm
  have hz : signedSum A weight - B * signedCard A weight = 0 := by
    apply eq_zero_of_dvd_of_abs_lt (mul_pos hB hd) _ hb
    refine ⟨-k, ?_⟩
    rw [hs, hk]
    ring
  have hmul : B * signedCard A weight = 0 := by omega
  exact (mul_eq_zero.mp hmul).resolve_left hB.ne'

/-- Subsets of a finite stage with equal sums have equal cardinalities. -/
theorem invariant.card_eq_of_sum_eq {A U V : Finset ℤ} {B h d : ℤ}
    (hi : invariant A B h d) (hB : 0 < B) (hd : 0 < d) (hm : mass A B < B * d)
    (hU : U ⊆ A) (hV : V ⊆ A)
    (hs : (∑ x ∈ U, x) = ∑ x ∈ V, x) : U.card = V.card := by
  let weight (x : ℤ) : ℤ := (if x ∈ U then 1 else 0) - (if x ∈ V then 1 else 0)
  have hw (x : ℤ) (_ : x ∈ A) : |weight x| ≤ 1 := by
    by_cases h₁ : x ∈ U <;> by_cases h₂ : x ∈ V <;> simp [weight, h₁, h₂]
  have hAU : A ∩ U = U := Finset.inter_eq_right.mpr hU
  have hAV : A ∩ V = V := Finset.inter_eq_right.mpr hV
  have hsum : signedSum A weight = 0 := by
    simp only [signedSum, weight, sub_mul, ite_mul, one_mul, zero_mul,
      Finset.sum_sub_distrib, Finset.sum_ite_mem, hAU, hAV, hs, sub_self]
  have hc := hi.signedCard_eq_zero hB hd hm weight hw hsum
  have heq : (U.card : ℤ) - (V.card : ℤ) = 0 := by
    simpa only [signedCard, weight, Finset.sum_sub_distrib, Finset.sum_ite_mem, hAU, hAV,
      Finset.sum_const, nsmul_eq_mul, mul_one] using hc
  exact_mod_cast sub_eq_zero.mp heq

/-- Appending terms congruent to the reference preserves the invariant at the old modulus. -/
theorem invariant.union_of_dvd_sub {A C : Finset ℤ} {B h d : ℤ}
    (hi : invariant A B h d) (hdisj : Disjoint A C)
    (hC : ∀ x ∈ C, h ∣ x - B) : invariant (A ∪ C) B h d := by
  intro weight hw q hdiv
  have hdev : h ∣ signedSum C weight - B * signedCard C weight := by
    unfold signedSum signedCard
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.dvd_sum
    intro x hx
    rw [show weight x * x - B * weight x = weight x * (x - B) by ring]
    exact dvd_mul_of_dvd_right (hC x hx) (weight x)
  have hsum :
      signedSum (A ∪ C) weight = signedSum A weight + signedSum C weight :=
    Finset.sum_union hdisj
  have hcard :
      signedCard (A ∪ C) weight = signedCard A weight + signedCard C weight :=
    Finset.sum_union hdisj
  have hv : h ∣ signedSum A weight + B * (signedCard C weight + q) := by
    convert dvd_sub hdiv hdev using 1
    rw [hsum]
    ring
  have hresult :=
    hi weight (fun x hx => hw x (Finset.mem_union_left C hx)) (signedCard C weight + q) hv
  rw [hcard, add_assoc]
  exact hresult

/-- A small signed remainder upgrades the period from `d` to its multiple `K`. -/
theorem invariant.refine_modulus {A : Finset ℤ} {B h d K : ℤ}
    (hi : invariant A B h d) (hB : 0 < B) (hd : 0 < d) (hK : d ∣ K)
    (hh : h ∣ B * K)
    (hrep : ∀ (weight : ℤ → ℤ), (∀ x ∈ A, |weight x| ≤ 1) →
      ∃ I Δ : ℤ, signedSum A weight = B * signedCard A weight + B * K * I + Δ ∧
        |Δ| < B * d) :
    invariant A B (B * K) K := by
  intro weight hw q hdiv
  obtain ⟨I, Δ, hsum, hΔ⟩ := hrep weight hw
  obtain ⟨j, hj⟩ := hi weight hw q (dvd_trans hh hdiv)
  obtain ⟨k, hk⟩ := hK
  obtain ⟨z, hz⟩ := hdiv
  have heq : B * (signedCard A weight + q) + B * K * I + Δ = B * K * z := by
    calc
      _ = signedSum A weight + B * q := by rw [hsum]; ring
      _ = _ := hz
  have hΔeq : Δ = B * d * (k * z - j - k * I) := by
    calc
      Δ = B * K * z - B * (signedCard A weight + q) - B * K * I := by omega
      _ = _ := by rw [hj, hk]; ring
  have hzero := eq_zero_of_dvd_of_abs_lt (mul_pos hB hd) ⟨_, hΔeq⟩ hΔ
  refine ⟨z - I, ?_⟩
  apply mul_left_cancel₀ hB.ne'
  calc
    B * (signedCard A weight + q) = B * K * z - B * K * I := by omega
    _ = B * (K * (z - I)) := by ring

/-- A change of reference by a multiple of the modulus preserves the invariant. -/
theorem invariant.change_reference {A : Finset ℤ} {B B' h d : ℤ}
    (hi : invariant A B h d) (hB : h ∣ B' - B) : invariant A B' h d := by
  intro weight hw q hsum
  apply hi weight hw q
  have hdiff : h ∣ (B' - B) * q := dvd_mul_of_dvd_left hB q
  convert dvd_sub hsum hdiff using 1; ring

end Jsp000726.Upper
