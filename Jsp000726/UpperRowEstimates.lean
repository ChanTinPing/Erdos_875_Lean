module

public import Jsp000726.UpperRows
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Cast.Order.Field

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators

namespace Jsp000726.Upper

private theorem offset_sum_tail_le {N r H : ℕ} (hN : 2 ≤ N) (m : ℕ) :
    (∑ j ∈ Finset.range m, (rowOffset N r H (N + j) : ℝ)) ≤ 2 * (N : ℝ) ^ 2 := by
  have hNR : 2 ≤ (N : ℝ) := by exact_mod_cast hN
  let f (j : ℕ) : ℝ := (N : ℝ) ^ 3 / ((N : ℝ) + j - 1)
  have hpoint j : (rowOffset N r H (N + j) : ℝ) ≤ f j - f (j + 1) := by
    have hj : 0 < N + j := by omega
    have hx : 1 < (N : ℝ) + (j : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) j
      linarith
    have hx' : 0 < (N : ℝ) + (j : ℝ) - 1 := by linarith
    have hx0 : 0 < (N : ℝ) + (j : ℝ) := by linarith
    have hdiv :
        ((N ^ 3 / (N + j) ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) ^ 3 / ((N : ℝ) + (j : ℝ)) ^ 2 := by
      simpa only [Nat.cast_add, Nat.cast_pow] using
        (Nat.cast_div_le : ((N ^ 3 / (N + j) ^ 2 : ℕ) : ℝ) ≤
          ((N ^ 3 : ℕ) : ℝ) / (((N + j) ^ 2 : ℕ) : ℝ))
    calc
      _ ≤ ((N ^ 3 / (N + j) ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast rowOffset_le_div (r := r) (H := H) (i := N + j) (by omega) hj
      _ ≤ (N : ℝ) ^ 3 / ((N : ℝ) + (j : ℝ)) ^ 2 := hdiv
      _ ≤ (N : ℝ) ^ 3 / (((N : ℝ) + (j : ℝ) - 1) * ((N : ℝ) + (j : ℝ))) := by
        apply div_le_div_of_nonneg_left (by positivity) (mul_pos hx' hx0)
        nlinarith
      _ = f j - f (j + 1) := by
        simp only [f, Nat.cast_add, Nat.cast_one]
        rw [show (N : ℝ) + ((j : ℝ) + 1) - 1 = (N : ℝ) + (j : ℝ) by ring]
        field_simp
        ring
  have htel (t : ℕ) : (∑ j ∈ Finset.range t, (f j - f (j + 1))) = f 0 - f t := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  calc
    _ ≤ ∑ j ∈ Finset.range m, (f j - f (j + 1)) :=
      Finset.sum_le_sum fun j _ => hpoint j
    _ = f 0 - f m := htel m
    _ ≤ f 0 := by
      have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      have hden : 0 < (N : ℝ) + (m : ℝ) - 1 := by linarith
      exact sub_le_self _ (div_nonneg (by positivity) hden.le)
    _ ≤ 2 * (N : ℝ) ^ 2 := by
      simp only [f, Nat.cast_zero, add_zero]
      apply (div_le_iff₀ (by linarith)).2
      nlinarith only [mul_nonneg (sq_nonneg (N : ℝ)) (show 0 ≤ (N : ℝ) - 2 by linarith)]

/-- The total within-row offset is bounded by three times the squared prefix length. -/
theorem rowOffset_sum_le {N r H : ℕ} (hN : 2 ≤ N) :
    (∑ j ∈ Finset.range r, rowOffset N r H j) ≤ 3 * N ^ 2 := by
  have hsum (m : ℕ) :
      (∑ j ∈ Finset.range m, rowOffset N r H j) ≤ m * N := by
    calc
      _ ≤ ∑ _j ∈ Finset.range m, N :=
        Finset.sum_le_sum fun j _ => (rowOffset_lt (r := r) (H := H) (i := j) (by omega)).le
      _ = m * N := by simp
  rcases le_total r N with hr | hr
  · calc
      _ ≤ r * N := hsum r
      _ ≤ N * N := Nat.mul_le_mul_right N hr
      _ ≤ 3 * N ^ 2 := by rw [pow_two]; omega
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hr
  nth_rw 1 [hm]
  rw [Finset.sum_range_add]
  have ht : (∑ j ∈ Finset.range m, rowOffset N r H (N + j)) ≤ 2 * N ^ 2 := by
    have htR := offset_sum_tail_le (r := r) (H := H) hN m
    rw [← Nat.cast_sum] at htR
    exact_mod_cast htR
  have h₁ := hsum N
  rw [pow_two] at ht ⊢
  omega

private theorem cast_quotient_increment_le {x y D : ℕ} (hD : 0 < D) :
    ((x / D : ℕ) : ℝ) - ((y / D : ℕ) : ℝ) ≤ 1 + ((x : ℝ) - y) / D := by
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  have h₁ : ((x / D : ℕ) : ℝ) ≤ (x : ℝ) / D := Nat.cast_div_le
  have h₂ : (y : ℝ) / D < ((y / D : ℕ) : ℝ) + 1 := by
    apply (div_lt_iff₀ hDR).2
    exact_mod_cast (show y < (y / D + 1) * D by
      simpa only [mul_comm] using Nat.lt_mul_div_succ y hD)
  rw [sub_div]
  linarith

private theorem cubic_increment_le {x : ℝ} (hx : 0 ≤ x) :
    (x + 1) ^ 3 - x ^ 3 ≤ 3 * (x + 1) ^ 2 := by
  nlinarith

private theorem seventh_increment_le {x : ℝ} (hx : 0 ≤ x) :
    (x + 1) ^ 7 - x ^ 7 ≤ 7 * (x + 1) ^ 6 := by
  apply sub_nonneg.mp
  rw [show 7 * (x + 1) ^ 6 - ((x + 1) ^ 7 - x ^ 7) =
    21 * x ^ 5 + 70 * x ^ 4 + 105 * x ^ 3 + 84 * x ^ 2 + 35 * x + 6 by ring]
  positivity

/-- The integer row increments are controlled by the derivatives of the two powers. -/
theorem rowIndex_gap_le {N r H i : ℕ} (hN : 0 < N) (hr : 0 < r) :
    ((rowIndex N r H (i + 1) - rowIndex N r H i : ℕ) : ℝ) ≤
      2 + 3 * ((i : ℝ) + 1) ^ 2 / (N : ℝ) ^ 3 +
        (H : ℝ) * (7 * ((i : ℝ) + 1) ^ 6) / (r : ℝ) ^ 7 := by
  have hmono := rowIndex_mono N r H (Nat.le_succ i)
  rw [Nat.cast_sub hmono]
  unfold rowIndex
  push_cast
  have h₁ := cast_quotient_increment_le
    (x := (i + 1) ^ 3) (y := i ^ 3) (D := N ^ 3) (Nat.pow_pos hN)
  have h₂ := cast_quotient_increment_le
    (x := H * (i + 1) ^ 7) (y := H * i ^ 7) (D := r ^ 7) (Nat.pow_pos hr)
  push_cast at h₁ h₂
  have h₁' := div_le_div_of_nonneg_right (cubic_increment_le (Nat.cast_nonneg i))
    (pow_nonneg (Nat.cast_nonneg (α := ℝ) N) 3)
  have h₂' := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (seventh_increment_le (Nat.cast_nonneg i)) (Nat.cast_nonneg H))
    (pow_nonneg (Nat.cast_nonneg (α := ℝ) r) 7)
  rw [mul_sub] at h₂'
  linarith only [h₁, h₂, h₁', h₂']

/-- Gaps between adjacent fillers are controlled by the same derivative estimate. -/
theorem fillerValue_gap_le_real {B g h N r H i : ℕ} (hN : 0 < N) (hr : 0 < r) :
    ((fillerValue B g h N r H (i + 1) - fillerValue B g h N r H i : ℕ) : ℝ) ≤
      (h : ℝ) + (g : ℝ) * (2 + 3 * ((i : ℝ) + 1) ^ 2 / (N : ℝ) ^ 3 +
        (H : ℝ) * (7 * ((i : ℝ) + 1) ^ 6) / (r : ℝ) ^ 7) := by
  have hg := fillerValue_gap_le (B := B) (g := g) (h := h)
    (N := N) (r := r) (H := H) (i := i)
  calc
    _ ≤ (h : ℝ) + (g : ℝ) * ((rowIndex N r H (i + 1) - rowIndex N r H i : ℕ) : ℝ) :=
      by exact_mod_cast hg
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left (rowIndex_gap_le hN hr)
      (Nat.cast_nonneg g)) (h : ℝ)

end Jsp000726.Upper
