module

public import Jsp000726.LowerRankTwoChains
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

namespace Jsp000726

private theorem cast_natAbs_real (x : ℤ) : (x.natAbs : ℝ) = |(x : ℝ)| := by
  rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]

/-- The integer capacity is the floor of the continuous capacity when the first
side binds. The two inequalities are stated without introducing a floor coercion. -/
theorem chainCapacity_binding_scale {x y : ℤ} {L₁ L₂ : ℕ} (h₁ : 0 < L₁) (h₂ : 0 < L₂)
    (hx : x ≠ 0)
    (hbind : |(y : ℝ)| * (((L₁ - 1 : ℕ) : ℝ) / |(x : ℝ)|) ≤ ((L₂ - 1 : ℕ) : ℝ)) :
    let scale := ((L₁ - 1 : ℕ) : ℝ) / |(x : ℝ)|
    (chainCapacity x y L₁ L₂ : ℝ) ≤ scale ∧
      scale < (chainCapacity x y L₁ L₂ : ℝ) + 1 := by
  intro scale
  let q := (L₁ - 1) / x.natAbs
  have hAbs : 0 < x.natAbs := Int.natAbs_pos.mpr hx
  have hAbsReal : 0 < |(x : ℝ)| := by rw [← cast_natAbs_real]; exact_mod_cast hAbs
  have hq₁ : q * x.natAbs ≤ L₁ - 1 := by
    simpa only [q, Nat.mul_comm] using Nat.mul_div_le (L₁ - 1) x.natAbs
  have hqt : (q : ℝ) ≤ scale := by
    apply (le_div_iff₀ hAbsReal).2
    rw [← cast_natAbs_real, ← Nat.cast_mul]
    exact_mod_cast hq₁
  have hq₂R : (q : ℝ) * |(y : ℝ)| ≤ ((L₂ - 1 : ℕ) : ℝ) := by
    calc
      _ ≤ scale * |(y : ℝ)| := mul_le_mul_of_nonneg_right hqt (abs_nonneg _)
      _ = |(y : ℝ)| * scale := mul_comm _ _
      _ ≤ _ := hbind
  have hq₂ : q * y.natAbs ≤ L₂ - 1 := by
    rw [← cast_natAbs_real, ← Nat.cast_mul] at hq₂R
    exact_mod_cast hq₂R
  have hcap := le_chainCapacity_iff (x := x) (y := y) (t := q) h₁ h₂ (Or.inl hx)
  have hcq : chainCapacity x y L₁ L₂ = q := by
    apply le_antisymm
    · apply (Nat.le_div_iff_mul_le hAbs).2
      have hh := (le_chainCapacity_iff h₁ h₂ (Or.inl hx)).1
        (show chainCapacity x y L₁ L₂ ≤ chainCapacity x y L₁ L₂ from le_rfl)
      omega
    · exact hcap.2 ⟨by omega, by omega⟩
  rw [hcq]
  refine ⟨hqt, (div_lt_iff₀ hAbsReal).2 ?_⟩
  have hu : L₁ - 1 < (q + 1) * x.natAbs := by
    simpa only [q, Nat.mul_comm] using Nat.lt_mul_div_succ (L₁ - 1) hAbs
  have huc : ((L₁ - 1 : ℕ) : ℝ) < (((q + 1) * x.natAbs : ℕ) : ℝ) := by exact_mod_cast hu
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, cast_natAbs_real] using huc

end Jsp000726
