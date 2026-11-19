module

public import Jsp000726.Basic

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

@[expose] public section

namespace Jsp000726.Upper

noncomputable def sharpS : ℝ := (gapThreshold - 1) / 2

noncomputable def sharpRho : ℝ := sharpS + 1

theorem sharpS_bounds : 3 / 2 < sharpS ∧ sharpS < 2 := by
  have hlo : (4 : ℝ) < Real.sqrt 17 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hhi : Real.sqrt 17 < (5 : ℝ) := (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  unfold sharpS gapThreshold
  constructor <;> linarith

theorem sharpRho_bounds : 5 / 2 < sharpRho ∧ sharpRho < 3 := by
  unfold sharpRho
  exact ⟨by linarith [sharpS_bounds.1], by linarith [sharpS_bounds.2]⟩

theorem gapThreshold_eq : gapThreshold = 2 * sharpS + 1 := by
  unfold sharpS
  linarith

theorem sharpS_polynomial : 2 * sharpS ^ 2 - 3 * sharpS - 1 = 0 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
  unfold sharpS gapThreshold
  nlinarith only [h]

theorem sharp_exponent_gap : sharpS + sharpRho = gapThreshold := by
  rw [gapThreshold_eq]
  unfold sharpRho
  linarith

theorem sharp_exponent_contract : sharpS * (2 * (sharpRho - 2)) = sharpRho := by
  unfold sharpRho
  nlinarith only [sharpS_polynomial]

theorem sharp_exponent_filler : sharpS * (gapThreshold - 3) = sharpRho := by
  rw [gapThreshold_eq]
  unfold sharpRho
  nlinarith only [sharpS_polynomial]

/-- Number of filler terms at a stage whose existing length is `N`. -/
noncomputable def sharpR (N : ℕ) : ℕ := ⌈(N : ℝ) ^ sharpS⌉₊

theorem rpow_le_sharpR (N : ℕ) : (N : ℝ) ^ sharpS ≤ (sharpR N : ℝ) :=
  Nat.le_ceil _

theorem le_sharpR {N : ℕ} (hN : 0 < N) : N ≤ sharpR N := by
  exact_mod_cast (Real.self_le_rpow_of_one_le (Nat.one_le_cast.mpr hN)
    (by linarith [sharpS_bounds.1])).trans (rpow_le_sharpR N)

theorem sharpR_pos {N : ℕ} (hN : 0 < N) : 0 < sharpR N := hN.trans_le (le_sharpR hN)

theorem sharpR_le_sq {N : ℕ} (hN : 0 < N) : sharpR N ≤ N ^ 2 := by
  apply Nat.ceil_le.mpr
  rw [Nat.cast_pow, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hN)
    (by simpa using sharpS_bounds.2.le)

theorem sharpR_le_two_rpow {N : ℕ} (hN : 0 < N) :
    (sharpR N : ℝ) ≤ 2 * (N : ℝ) ^ sharpS := by
  have hpow : 1 ≤ (N : ℝ) ^ sharpS :=
    Real.one_le_rpow (Nat.one_le_cast.mpr hN) (by linarith [sharpS_bounds.1])
  have hceil : (sharpR N : ℝ) < (N : ℝ) ^ sharpS + 1 := Nat.ceil_lt_add_one (by positivity)
  linarith

end Jsp000726.Upper
