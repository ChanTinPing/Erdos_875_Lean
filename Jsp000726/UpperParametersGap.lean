module

public import Jsp000726.UpperParametersReal

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726.Upper

private theorem cubic_row_bound {N x : ℝ} (hN : 1 ≤ N) (hx : 0 ≤ x) :
    x ^ 2 / N ^ 3 ≤ (N + x) ^ gapThreshold / N ^ gapThreshold := by
  have hN₀ := zero_lt_one.trans_le hN
  have hz : 1 ≤ (N + x) / N := by
    apply (le_div_iff₀ hN₀).2
    linarith
  have hcpp : (2 : ℝ) ≤ gapThreshold := by linarith [gapThreshold_eq, sharpS_bounds.1]
  have hNp : N ^ (2 : ℕ) ≤ N ^ (3 : ℕ) := pow_le_pow_right₀ hN (by decide)
  calc
    x ^ 2 / N ^ 3 ≤ x ^ 2 / N ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hN₀ _) hNp
    _ ≤ (N + x) ^ 2 / N ^ 2 := div_le_div_of_nonneg_right
      (pow_le_pow_left₀ hx (by linarith) 2) (sq_nonneg _)
    _ = ((N + x) / N) ^ (2 : ℝ) := by rw [Real.rpow_ofNat, div_pow]
    _ ≤ ((N + x) / N) ^ gapThreshold := Real.rpow_le_rpow_of_exponent_le hz hcpp
    _ = _ := Real.div_rpow (by linarith) hN₀.le gapThreshold

private theorem seventh_row_bound {N x r : ℝ} (hN : 1 ≤ N) (hx : 0 ≤ x) (hr : 0 < r)
    (hxr : x ≤ r) : x ^ 6 / r ^ 7 ≤ (N + x) ^ gapThreshold / r ^ (gapThreshold + 1) := by
  have hc : 0 ≤ gapThreshold := by linarith [gapThreshold_eq, sharpS_bounds.1]
  have hd : 0 ≤ 6 - gapThreshold := by linarith [gapThreshold_eq, sharpS_bounds.2]
  have hpower : x ^ (6 : ℕ) ≤ (N + x) ^ gapThreshold * r ^ (6 - gapThreshold) := by
    conv_lhs => rw [← Real.rpow_ofNat, show (6 : ℝ) = gapThreshold + (6 - gapThreshold) by ring,
      Real.rpow_add_of_nonneg hx hc hd]
    exact mul_le_mul (Real.rpow_le_rpow hx (by linarith) hc)
      (Real.rpow_le_rpow hx hxr hd) (Real.rpow_nonneg hx _) (Real.rpow_nonneg (by linarith) _)
  have hex : r ^ (6 - gapThreshold) / r ^ (7 : ℕ) = 1 / r ^ (gapThreshold + 1) := by
    rw [← Real.rpow_ofNat, ← Real.rpow_sub hr,
      show (6 - gapThreshold - 7) = -(gapThreshold + 1) by ring,
      Real.rpow_neg hr.le, one_div]
  calc
    _ ≤ ((N + x) ^ gapThreshold * r ^ (6 - gapThreshold)) / r ^ (7 : ℕ) :=
      div_le_div_of_nonneg_right hpower (pow_nonneg hr.le _)
    _ = _ := by rw [mul_div_assoc, hex, mul_one_div]

/-- The row step estimate implies a gap bound at the sharp exponent with a fixed,
stage-normalized coefficient. The same bound handles a step within one row
or within the dense block. -/
theorem normalized_row_gap_bound {N x r D h g H B' : ℝ} (hN : 1 ≤ N) (hx : 0 ≤ x)
    (hr : 0 < r) (hxr : x ≤ r) (hh : h ≤ g) (hg : 0 ≤ g) (hH : 0 ≤ H)
    (hB' : g * H ≤ B')
    (hD : D ≤ h + g * (2 + 3 * x ^ 2 / N ^ 3 + H * 7 * x ^ 6 / r ^ 7)) :
    D / (N + x) ^ gapThreshold ≤
      6 * g / N ^ gapThreshold + 7 * B' / r ^ (gapThreshold + 1) := by
  have hN₀ := zero_lt_one.trans_le hN
  have hM₀ : 0 < N + x := by linarith
  have hM := Real.rpow_pos_of_pos hM₀ gapThreshold
  have hc : 0 ≤ gapThreshold := by linarith [gapThreshold_eq, sharpS_bounds.1]
  have hratio : 1 ≤ (N + x) ^ gapThreshold / N ^ gapThreshold :=
    (le_div_iff₀ (Real.rpow_pos_of_pos hN₀ _)).2
      (by simpa only [one_mul] using Real.rpow_le_rpow hN₀.le (by linarith) hc)
  have h₁ := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 3 * g by positivity)
  have h₂ := mul_le_mul_of_nonneg_left (cubic_row_bound hN hx) (show 0 ≤ 3 * g by positivity)
  have h₃ := mul_le_mul_of_nonneg_left (seventh_row_bound hN hx hr hxr)
    (show 0 ≤ 7 * (g * H) by positivity)
  have h₄ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB' (by norm_num : (0 : ℝ) ≤ 7))
    (div_nonneg hM.le (Real.rpow_nonneg hr.le (gapThreshold + 1)))
  apply (div_le_iff₀ hM).2
  calc
    D ≤ h + g * (2 + 3 * x ^ 2 / N ^ 3 + H * 7 * x ^ 6 / r ^ 7) := hD
    _ = h + 2 * g + 3 * g * (x ^ 2 / N ^ 3) + 7 * (g * H) * (x ^ 6 / r ^ 7) := by ring
    _ ≤ 3 * g * ((N + x) ^ gapThreshold / N ^ gapThreshold) +
        3 * g * ((N + x) ^ gapThreshold / N ^ gapThreshold) +
        7 * B' * ((N + x) ^ gapThreshold / r ^ (gapThreshold + 1)) := by
      have hsmall : h + 2 * g ≤ 3 * g := by linarith
      exact add_le_add (add_le_add (by simpa using hsmall.trans (by simpa using h₁)) h₂)
        (h₃.trans h₄)
    _ = _ := by ring

/-- A sufficiently small normalized reference makes each admissible row step
obey the coefficient-one sharp gap cap. -/
theorem sharp_gap_cap_of_row {N x r C B D h g H B' : ℝ} (hN : 1 ≤ N) (hx : 0 ≤ x)
    (hB : 0 ≤ B) (hrlo : N ^ sharpS ≤ r) (hrhi : r ≤ 2 * N ^ sharpS) (hxr : x ≤ r)
    (hh : h ≤ g) (hg₀ : 0 ≤ g) (hH : 0 ≤ H) (hB'H : g * H ≤ B')
    (hg : g ≤ 17 * B * r) (hB' : B' ≤ 65 * B * C ^ 2 * r ^ 4)
    (hsmall : (204 + 455 * C ^ 2) * (B / N ^ sharpRho) ≤ 1)
    (hD : D ≤ h + g * (2 + 3 * x ^ 2 / N ^ 3 + H * 7 * x ^ 6 / r ^ 7)) :
    D ≤ (N + x) ^ gapThreshold := by
  have hN₀ : 0 < N := zero_lt_one.trans_le hN
  have hr : 0 < r := (Real.rpow_pos_of_pos hN₀ sharpS).trans_le hrlo
  have hcap := (normalized_row_gap_bound hN hx hr hxr hh hg₀ hH hB'H hD).trans
    ((normalized_gap_coefficients hN₀ hB hrlo hrhi hg hB').trans hsmall)
  have hpos : 0 < (N + x) ^ gapThreshold := Real.rpow_pos_of_pos (by linarith) _
  simpa only [one_mul] using (div_le_iff₀ hpos).mp hcap

/-- A constant step of size `g` obeys the sharp cap at every index at least `N`. -/
theorem sharp_dense_gap_cap {N M r C B g B' : ℝ} (hN : 1 ≤ N) (hM : N ≤ M)
    (hB : 0 ≤ B) (hrlo : N ^ sharpS ≤ r) (hrhi : r ≤ 2 * N ^ sharpS)
    (hg₀ : 0 ≤ g) (hB'₀ : 0 ≤ B')
    (hg : g ≤ 17 * B * r) (hB' : B' ≤ 65 * B * C ^ 2 * r ^ 4)
    (hsmall : (204 + 455 * C ^ 2) * (B / N ^ sharpRho) ≤ 1) :
    g ≤ M ^ gapThreshold := by
  have hr : 0 ≤ r := (Real.rpow_nonneg (zero_le_one.trans hN) sharpS).trans hrlo
  have hcap := sharp_gap_cap_of_row (x := 0) (D := g) (h := 0) (H := 0)
    hN le_rfl hB hrlo hrhi hr hg₀ hg₀ le_rfl
    (by simpa only [mul_zero] using hB'₀) hg hB' hsmall (by
      simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (6 : ℕ) ≠ 0),
        mul_zero, zero_div, add_zero, zero_add]
      linarith)
  have hmon := Real.rpow_le_rpow (zero_le_one.trans hN) hM
    (show 0 ≤ gapThreshold by linarith [gapThreshold_eq, sharpS_bounds.1])
  exact (by simpa only [add_zero] using hcap : g ≤ N ^ gapThreshold).trans hmon

end Jsp000726.Upper
