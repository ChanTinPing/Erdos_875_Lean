module

public import Jsp000726.LowerRankTwo

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726

/-- With the first side binding the primitive chain length, the drift parameter forces
the second generator to separate the chain labels. -/
theorem rankTwo_long_generator_lower_bound {R M X Y scale a b g₁ g₂ : ℝ}
    (hR : 0 ≤ R) (hY : 0 < Y) (hscale : 0 ≤ scale) (ha : a ≠ 0)
    (hX : |a| * scale = X) (hYscale : |b| * scale ≤ Y)
    (hXY : X * Y ≤ M) (hscaleM : scale ≤ M)
    (hspan : |g₁| * X + |g₂| * Y = R * M)
    (hshort : |a * g₁ + b * g₂| ≤ R / 10) :
    (45 / 100 : ℝ) * (R * scale) ≤ |g₂ / a| := by
  have htri : |a| * |g₁| ≤ |a * g₁ + b * g₂| + |b| * |g₂| := by
    simpa only [add_sub_cancel_right, sub_zero, zero_sub, abs_neg, abs_mul] using
      abs_sub_le (a * g₁ + b * g₂) 0 (b * g₂)
  have hgX : |g₁| * X ≤ (R / 10) * M + |g₂| * Y := by
    calc
      |g₁| * X = (|a| * |g₁|) * scale := by rw [← hX]; ring
      _ ≤ (|a * g₁ + b * g₂| + |b| * |g₂|) * scale :=
        mul_le_mul_of_nonneg_right htri hscale
      _ = |a * g₁ + b * g₂| * scale + |g₂| * (|b| * scale) := by ring
      _ ≤ _ := add_le_add
        (mul_le_mul hshort hscaleM hscale (div_nonneg hR (by norm_num)))
        (mul_le_mul_of_nonneg_left hYscale (abs_nonneg g₂))
  have hGY : (45 / 100 : ℝ) * (R * M) ≤ |g₂| * Y := by
    linarith only [hgX, hspan]
  have hG : ((45 / 100 : ℝ) * (R * scale) * |a|) * Y ≤ |g₂| * Y := by
    calc
      _ = (45 / 100 : ℝ) * R * (X * Y) := by rw [← hX]; ring
      _ ≤ (45 / 100 : ℝ) * R * M := mul_le_mul_of_nonneg_left hXY (by positivity)
      _ = (45 / 100 : ℝ) * (R * M) := by ring
      _ ≤ _ := hGY
  rw [abs_div]
  exact (le_div_iff₀ (abs_pos.mpr ha)).mpr (le_of_mul_le_mul_right hG hY)

/-- Numeric values in different primitive chains are separated by a fixed part
of the average spacing times the maximum continuous chain length. -/
theorem rankTwo_chain_value_separation {R scale X a b g₁ g₂ x₁ x₂ y₁ y₂ : ℝ} {k l : ℤ}
    (ha : a ≠ 0) (hscale : 0 ≤ scale) (hX : |a| * scale = X)
    (hkl : k ≠ l)
    (hlabel : ((k - l : ℤ) : ℝ) = a * (x₂ - y₂) - b * (x₁ - y₁))
    (hgen : (45 / 100 : ℝ) * (R * scale) ≤ |g₂ / a|)
    (hshort : |a * g₁ + b * g₂| ≤ R / 10)
    (hcoords : |x₁ - y₁| ≤ X) :
    (35 / 100 : ℝ) * (R * scale) ≤ |(g₁ * x₁ + g₂ * x₂) - (g₁ * y₁ + g₂ * y₂)| := by
  have hdrift : |((a * g₁ + b * g₂) / a) * (x₁ - y₁)| ≤ (1 / 10 : ℝ) * (R * scale) := by
    rw [abs_mul, abs_div]
    calc
      _ ≤ (|a * g₁ + b * g₂| / |a|) * X :=
        mul_le_mul_of_nonneg_left hcoords (div_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = |a * g₁ + b * g₂| * scale := by
        rw [← hX, ← mul_assoc, div_mul_cancel₀ _ (abs_ne_zero.mpr ha)]
      _ ≤ (R / 10) * scale := mul_le_mul_of_nonneg_right hshort hscale
      _ = _ := by ring
  have hsep := distinct_rankTwo_chains_separated (x := x₁) (y := y₁) hkl hgen hdrift
  have hid : (g₂ / a) * ((k - l : ℤ) : ℝ) + ((a * g₁ + b * g₂) / a) * (x₁ - y₁) =
      (g₁ * x₁ + g₂ * x₂) - (g₁ * y₁ + g₂ * y₂) := by
    rw [hlabel]
    field_simp [ha]
    ring
  simpa only [hid] using hsep

/-- In a nontrivial box one of the two nonzero direction coordinates binds the chain length. -/
theorem rankTwo_binding_side {a b X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hdir : a ≠ 0 ∨ b ≠ 0) :
    (a ≠ 0 ∧ |b| * (X / |a|) ≤ Y) ∨ (b ≠ 0 ∧ |a| * (Y / |b|) ≤ X) := by
  by_cases ha : a = 0
  · right
    exact ⟨hdir.resolve_left (not_ne_iff.mpr ha), by simpa [ha] using hX⟩
  by_cases hb : b = 0
  · left
    exact ⟨ha, by simpa [hb] using hY⟩
  rcases le_total (X / |a|) (Y / |b|) with h | h
  · exact Or.inl ⟨ha, by rw [mul_comm]; exact (le_div_iff₀ (abs_pos.mpr hb)).mp h⟩
  · exact Or.inr ⟨hb, by rw [mul_comm]; exact (le_div_iff₀ (abs_pos.mpr ha)).mp h⟩

private theorem integer_segment_bounds (g : ℤ) {z N : ℤ} (hz₀ : 0 ≤ z) (hzN : z ≤ N) :
    min 0 (g * N) ≤ g * z ∧ g * z ≤ max 0 (g * N) := by
  by_cases hg : 0 ≤ g
  · exact ⟨(min_le_left _ _).trans (mul_nonneg hg hz₀),
      (mul_le_mul_of_nonneg_left hzN hg).trans (le_max_right _ _)⟩
  · have h : g ≤ 0 := le_of_not_ge hg
    exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hzN h),
      (mul_nonpos_of_nonpos_of_nonneg h hz₀).trans (le_max_left _ _)⟩

private theorem integer_segment_corners (g : ℤ) (X : ℕ) :
    (∃ lo : ℤ, 0 ≤ lo ∧ lo ≤ X ∧ g * lo = min 0 (g * X)) ∧
    (∃ hi : ℤ, 0 ≤ hi ∧ hi ≤ X ∧ g * hi = max 0 (g * X)) := by
  by_cases hg : 0 ≤ g
  · have h := mul_nonneg hg (Int.natCast_nonneg X)
    exact ⟨⟨0, le_rfl, Int.natCast_nonneg X, by simp [min_eq_left h]⟩,
      ⟨X, Int.natCast_nonneg X, le_rfl, (max_eq_right h).symm⟩⟩
  · have h := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hg) (Int.natCast_nonneg X)
    exact ⟨⟨X, Int.natCast_nonneg X, le_rfl, (min_eq_right h).symm⟩,
      ⟨0, le_rfl, Int.natCast_nonneg X, by simp [max_eq_left h]⟩⟩

private theorem int_max_sub_min (z : ℤ) : max 0 z - min 0 z = |z| := by
  by_cases hz : 0 ≤ z
  · simp [max_eq_right hz, min_eq_left hz, abs_of_nonneg hz]
  · have h := le_of_not_ge hz
    simp [max_eq_left h, min_eq_right h, abs_of_nonpos h]

/-- The span of a two-dimensional integer box is exactly the sum of the two absolute
generator contributions. Both ends are attained at corners. -/
theorem rankTwo_box_span (base g₁ g₂ : ℤ) (X Y : ℕ) :
    ∃ lo hi : ℤ,
      (∀ x y : ℤ, 0 ≤ x → x ≤ X → 0 ≤ y → y ≤ Y →
        lo ≤ base + g₁ * x + g₂ * y ∧ base + g₁ * x + g₂ * y ≤ hi) ∧
      (∃ x y : ℤ, 0 ≤ x ∧ x ≤ X ∧ 0 ≤ y ∧ y ≤ Y ∧
        base + g₁ * x + g₂ * y = lo) ∧
      (∃ x y : ℤ, 0 ≤ x ∧ x ≤ X ∧ 0 ≤ y ∧ y ≤ Y ∧
        base + g₁ * x + g₂ * y = hi) ∧
      hi - lo = |g₁| * X + |g₂| * Y := by
  let lo := base + min 0 (g₁ * X) + min 0 (g₂ * Y)
  let hi := base + max 0 (g₁ * X) + max 0 (g₂ * Y)
  obtain ⟨⟨xl, hxl₀, hxlX, hxl⟩, ⟨xh, hxh₀, hxhX, hxh⟩⟩ := integer_segment_corners g₁ X
  obtain ⟨⟨yl, hyl₀, hylY, hyl⟩, ⟨yh, hyh₀, hyhY, hyh⟩⟩ := integer_segment_corners g₂ Y
  refine ⟨lo, hi, ?_, ⟨xl, yl, hxl₀, hxlX, hyl₀, hylY, by simp [lo, hxl, hyl]⟩,
    ⟨xh, yh, hxh₀, hxhX, hyh₀, hyhY, by simp [hi, hxh, hyh]⟩, ?_⟩
  · intro x y hx₀ hxX hy₀ hyY
    obtain ⟨hx, hx'⟩ := integer_segment_bounds g₁ hx₀ hxX
    obtain ⟨hy, hy'⟩ := integer_segment_bounds g₂ hy₀ hyY
    dsimp [lo, hi]
    omega
  · dsimp [lo, hi]
    calc
      _ = (max 0 (g₁ * X) - min 0 (g₁ * X)) +
        (max 0 (g₂ * Y) - min 0 (g₂ * Y)) := by ring
      _ = _ := by simp [int_max_sub_min, abs_mul, abs_of_nonneg (Int.natCast_nonneg X),
          abs_of_nonneg (Int.natCast_nonneg Y)]

theorem rounded_chain_separation {R scale L d : ℝ} (hR : 0 ≤ R) (hscale : 1 ≤ scale)
    (hL : L ≤ scale + 1) (hsep : (35 / 100 : ℝ) * (R * scale) ≤ d) :
    (7 / 40 : ℝ) * R * L ≤ d := by
  have hbound : L ≤ 2 * scale := by linarith
  have hl := mul_le_mul_of_nonneg_left hbound (show 0 ≤ (7 / 40 : ℝ) * R by positivity)
  nlinarith only [hl, hsep]

end Jsp000726
