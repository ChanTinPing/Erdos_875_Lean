module

public import Jsp000726.LowerRankTwoChains
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726

/-- A nonzero projection of a difference parallel to the primitive direction
has absolute value at least one projected primitive step. -/
theorem int_collinear_spacing {x y a b g₁ g₂ : ℤ}
    (hbase : ∃ u v : ℤ, u * x + v * y = 1) (hdet : x * b = y * a)
    (hsep : g₁ * a + g₂ * b ≠ 0) :
    |g₁ * x + g₂ * y| ≤ |g₁ * a + g₂ * b| := by
  obtain ⟨m, ha, hb⟩ := int_collinear_multiple hbase hdet
  have hm : m ≠ 0 := by
    intro hm
    apply hsep
    simp [ha, hb, hm]
  have heq : g₁ * a + g₂ * b = m * (g₁ * x + g₂ * y) := by rw [ha, hb]; ring
  rw [heq, abs_mul]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (Int.one_le_abs hm) (abs_nonneg (g₁ * x + g₂ * y))

/-- If different labels are separated by at least `g`, a numerical window of
length `g` on the projected carrier has at most one chain's worth of points. -/
theorem projected_box_window_card_le {x y : ℤ} {L₁ L₂ g : ℕ}
    (h₁ : 0 < L₁) (h₂ : 0 < L₂) (hxy : x ≠ 0 ∨ y ≠ 0)
    (hbase : ∃ u v : ℤ, u * x + v * y = 1)
    (S : Finset (ℤ × ℤ)) (proj : (ℤ × ℤ) → ℕ)
    (box : ∀ p ∈ S, 0 ≤ p.1 ∧ p.1 < L₁ ∧ 0 ≤ p.2 ∧ p.2 < L₂)
    (hsep : ∀ p ∈ S, ∀ p' ∈ S, x * p.2 - y * p.1 ≠ x * p'.2 - y * p'.1 →
      proj p + g ≤ proj p' ∨ proj p' + g ≤ proj p)
    (z : ℕ) :
    ((S.image proj).filter fun t => t ≤ z ∧ z < t + g).card ≤
      chainCapacity x y L₁ L₂ + 1 := by
  let T := S.filter (fun p => proj p ≤ z ∧ z < proj p + g)
  have hT : T.image proj = (S.image proj).filter (fun t => t ≤ z ∧ z < t + g) := by
    ext t
    constructor
    · intro h
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hp₁, hp₂⟩ := Finset.mem_filter.mp (show p ∈ T from hp)
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨p, hp₁, rfl⟩, hp₂⟩
    · intro h
      obtain ⟨ht, hwin⟩ := Finset.mem_filter.mp h
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
      exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hwin⟩, rfl⟩
  rw [← hT]
  refine Finset.card_image_le.trans ?_
  by_cases hne : T.Nonempty
  · obtain ⟨p', hp'⟩ := hne
    obtain ⟨hs', hlo', hhi'⟩ := Finset.mem_filter.mp (show p' ∈ T from hp')
    apply card_box_chain_le h₁ h₂ hxy hbase T (x * p'.2 - y * p'.1)
      (fun p hp => box p (Finset.mem_filter.mp (show p ∈ T from hp)).1)
    intro p hp
    obtain ⟨hs, hlo, hhi⟩ := Finset.mem_filter.mp (show p ∈ T from hp)
    by_contra hh
    rcases hsep p hs p' hs' hh with h | h <;> omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

/-- A strict real separation above `H` gives an integer window cut at
`floor(H) + 1`, allowing translations by layers of total weight at most `H`. -/
theorem projected_box_window_card_le_of_real_separation {x y : ℤ} {L₁ L₂ : ℕ} {H : ℝ}
    (h₁ : 0 < L₁) (h₂ : 0 < L₂) (hxy : x ≠ 0 ∨ y ≠ 0)
    (hbase : ∃ u v : ℤ, u * x + v * y = 1)
    (S : Finset (ℤ × ℤ)) (proj : (ℤ × ℤ) → ℕ) (hH : 0 ≤ H)
    (box : ∀ p ∈ S, 0 ≤ p.1 ∧ p.1 < L₁ ∧ 0 ≤ p.2 ∧ p.2 < L₂)
    (hsep : ∀ p ∈ S, ∀ p' ∈ S, x * p.2 - y * p.1 ≠ x * p'.2 - y * p'.1 →
      H < |(proj p : ℝ) - (proj p' : ℝ)|)
    (z : ℕ) :
    ((S.image proj).filter fun t => t ≤ z ∧ z < t + (⌊H⌋₊ + 1)).card ≤
      chainCapacity x y L₁ L₂ + 1 := by
  apply projected_box_window_card_le h₁ h₂ hxy hbase S proj box _ z
  intro p hp p' hp' hlabel
  have hh := hsep p hp p' hp' hlabel
  rcases le_total (proj p) (proj p') with h | h
  · have hh' : H < ((proj p' - proj p : ℕ) : ℝ) := by
      rw [Nat.cast_sub h, ← abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr h)), abs_sub_comm]
      exact hh
    have hdist := (Nat.floor_lt hH).2 hh'
    exact Or.inl (by omega)
  · have hh' : H < ((proj p - proj p' : ℕ) : ℝ) := by
      rwa [Nat.cast_sub h, ← abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr h))]
    have hdist := (Nat.floor_lt hH).2 hh'
    exact Or.inr (by omega)

end Jsp000726
