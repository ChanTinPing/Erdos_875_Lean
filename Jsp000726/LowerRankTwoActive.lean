module

public import Jsp000726.LowerRankTwoGeometry
public import Jsp000726.LowerRankTwoChains

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726

/-- The discrete chain length is at most one plus the continuous binding scale. -/
theorem chainCapacity_succ_le_left_scale {a b : ℤ} {X Y : ℕ} (ha : a ≠ 0) :
    ((chainCapacity a b (X + 1) (Y + 1) + 1 : ℕ) : ℝ) ≤
      (X : ℝ) / |(a : ℝ)| + 1 := by
  let C := chainCapacity a b (X + 1) (Y + 1)
  have hC : C * a.natAbs < X + 1 :=
    ((le_chainCapacity_iff (by omega) (by omega) (Or.inl ha)).1
      (show C ≤ chainCapacity a b (X + 1) (Y + 1) from le_rfl)).1
  have hCast : (C : ℝ) * |(a : ℝ)| ≤ (X : ℝ) := by
    have h : C * a.natAbs ≤ X := by omega
    have hI : (C : ℤ) * |a| ≤ (X : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast h
    exact_mod_cast hI
  have hAbs : 0 < |(a : ℝ)| := abs_pos.mpr (by exact_mod_cast ha)
  push_cast
  exact add_le_add_left ((le_div_iff₀ hAbs).mpr hCast) 1

/-- The projected spacing for two distinct integer labels on a horizontal binding side. -/
theorem rankTwo_integer_separation_left {R g₁ g₂ : ℝ} {X Y : ℕ}
    {a b x₁ x₂ y₁ y₂ : ℤ} (hR : 0 ≤ R) (hY : 0 < Y) (ha : a ≠ 0)
    (hbind : |(b : ℝ)| * ((X : ℝ) / |(a : ℝ)|) ≤ (Y : ℝ))
    (hspan : |g₁| * (X : ℝ) + |g₂| * (Y : ℝ) = R * (((X : ℝ) + 1) * ((Y : ℝ) + 1)))
    (hshort : |(a : ℝ) * g₁ + (b : ℝ) * g₂| ≤ R / 10)
    (hcoords : |((x₁ - y₁ : ℤ) : ℝ)| ≤ (X : ℝ))
    (hlabel : a * x₂ - b * x₁ ≠ a * y₂ - b * y₁) :
    (35 / 100 : ℝ) * (R * ((X : ℝ) / |(a : ℝ)|)) ≤
      |(g₁ * (x₁ : ℝ) + g₂ * (x₂ : ℝ)) - (g₁ * (y₁ : ℝ) + g₂ * (y₂ : ℝ))| := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hAbs : 0 < |(a : ℝ)| := abs_pos.mpr ha'
  have hAbs1 : (1 : ℝ) ≤ |(a : ℝ)| := by exact_mod_cast Int.one_le_abs ha
  have hX0 : 0 ≤ (X : ℝ) := Nat.cast_nonneg X
  have hY0 : 0 ≤ (Y : ℝ) := Nat.cast_nonneg Y
  have hY' : 0 < (Y : ℝ) := by exact_mod_cast hY
  let w : ℝ := (X : ℝ) / |(a : ℝ)|
  let M : ℝ := ((X : ℝ) + 1) * ((Y : ℝ) + 1)
  have hw : 0 ≤ w := div_nonneg hX0 hAbs.le
  have hM : (X : ℝ) ≤ M := by
    dsimp [M]
    nlinarith only [hY0, mul_nonneg hX0 hY0]
  have hwM : w ≤ M := (div_le_self hX0 hAbs1).trans hM
  have hXY : (X : ℝ) * (Y : ℝ) ≤ M := by
    dsimp [M]
    nlinarith only [hX0, hY0]
  have heq : |(a : ℝ)| * w = (X : ℝ) := mul_div_cancel₀ _ hAbs.ne'
  have hg := rankTwo_long_generator_lower_bound hR hY' hw ha' heq hbind hXY hwM hspan hshort
  have hl : (((a * x₂ - b * x₁) - (a * y₂ - b * y₁) : ℤ) : ℝ) =
      (a : ℝ) * ((x₂ : ℝ) - y₂) - (b : ℝ) * ((x₁ : ℝ) - y₁) := by
    push_cast
    ring
  exact rankTwo_chain_value_separation ha' hw heq hlabel hl hg hshort
    (by simpa only [Int.cast_sub] using hcoords)

end Jsp000726
