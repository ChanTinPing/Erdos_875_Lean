module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Ring.Abs

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726

/-- In a rank-two progression with large average spacing, all coordinate differences
whose numerical values are short lie on one line. The determinant condition expresses
the integral coordinates. -/
theorem short_directions_parallel {R L₁ L₂ g₁ g₂ x₁ x₂ y₁ y₂ : ℝ}
    (hR : 0 < R) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (hgen : R * L₂ ≤ 2 * |g₁| ∨ R * L₁ ≤ 2 * |g₂|)
    (hx₁ : |x₁| ≤ L₁) (hy₁ : |y₁| ≤ L₁) (hx₂ : |x₂| ≤ L₂) (hy₂ : |y₂| ≤ L₂)
    (hx : |g₁ * x₁ + g₂ * x₂| ≤ R / 10) (hy : |g₁ * y₁ + g₂ * y₂| ≤ R / 10)
    (hint : x₁ * y₂ - x₂ * y₁ ≠ 0 → 1 ≤ |x₁ * y₂ - x₂ * y₁|) :
    x₁ * y₂ - x₂ * y₁ = 0 := by
  by_contra hne
  let d := x₁ * y₂ - x₂ * y₁
  let X := g₁ * x₁ + g₂ * x₂
  let Y := g₁ * y₁ + g₂ * y₂
  have hd : 1 ≤ |d| := hint hne
  have h0 : 0 ≤ R / 10 := by positivity
  have ha : g₁ * d = X * y₂ - Y * x₂ := by dsimp [d, X, Y]; ring
  have hb : g₂ * d = x₁ * Y - y₁ * X := by dsimp [d, X, Y]; ring
  have hA : |g₁| ≤ R * L₂ / 5 := calc
    |g₁| ≤ |g₁| * |d| := by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hd (abs_nonneg g₁)
    _ = |g₁ * d| := (abs_mul _ _).symm
    _ = |X * y₂ - Y * x₂| := congrArg abs ha
    _ ≤ |X| * |y₂| + |Y| * |x₂| := by
      simpa only [sub_zero, zero_sub, abs_neg, abs_mul] using abs_sub_le (X * y₂) 0 (Y * x₂)
    _ ≤ (R / 10) * L₂ + (R / 10) * L₂ := add_le_add
      (mul_le_mul hx hy₂ (abs_nonneg _) h0)
      (mul_le_mul hy hx₂ (abs_nonneg _) h0)
    _ = _ := by ring
  have hB : |g₂| ≤ R * L₁ / 5 := calc
    |g₂| ≤ |g₂| * |d| := by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hd (abs_nonneg g₂)
    _ = |g₂ * d| := (abs_mul _ _).symm
    _ = |x₁ * Y - y₁ * X| := congrArg abs hb
    _ ≤ |x₁| * |Y| + |y₁| * |X| := by
      simpa only [sub_zero, zero_sub, abs_neg, abs_mul] using abs_sub_le (x₁ * Y) 0 (y₁ * X)
    _ ≤ L₁ * (R / 10) + L₁ * (R / 10) := add_le_add
      (mul_le_mul hx₁ hy (abs_nonneg _) hL₁.le)
      (mul_le_mul hy₁ hx (abs_nonneg _) hL₁.le)
    _ = _ := by ring
  rcases hgen with hg | hg
  · linarith only [hA, hg, mul_pos hR hL₂]
  · linarith only [hB, hg, mul_pos hR hL₁]

/-- Distinct parallel chain labels leave a gap after subtracting the maximum drift
within a chain. -/
theorem distinct_rankTwo_chains_separated {d A B x y : ℝ} {k l : ℤ}
    (hkl : k ≠ l) (hA : (45 / 100 : ℝ) * d ≤ |A|)
    (hB : |B * (x - y)| ≤ (1 / 10 : ℝ) * d) :
    (35 / 100 : ℝ) * d ≤ |A * (k - l : ℤ) + B * (x - y)| := by
  have h1 : (1 : ℝ) ≤ |((k - l : ℤ) : ℝ)| := by
    exact_mod_cast (Int.one_le_abs (sub_ne_zero.mpr hkl))
  have hmain : |A| ≤ |A * (k - l : ℤ)| := by
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h1 (abs_nonneg A)
  let M : ℝ := A * (k - l : ℤ)
  let E : ℝ := B * (x - y)
  have htri : |M| ≤ |M + E| + |E| := by
    simpa only [add_sub_cancel_right, sub_zero, zero_sub, abs_neg] using abs_sub_le (M + E) 0 E
  change (35 / 100 : ℝ) * d ≤ |M + E|
  change |A| ≤ |M| at hmain
  change |E| ≤ (1 / 10 : ℝ) * d at hB
  linarith only [hmain, htri, hA, hB]

end Jsp000726
