module

public import Jsp000726.UpperParameters

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726.Upper

/-- A common integer factor suffices for strict normalization contraction. -/
theorem sharp_fixed_factor : (65 : ℝ) * (16900 : ℝ) ^ (2 - sharpRho) ≤ 1 / 2 := by
  have hroot : Real.sqrt (16900 : ℝ) = 130 := by
    rw [show (16900 : ℝ) = 130 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num)]
  calc
    (65 : ℝ) * (16900 : ℝ) ^ (2 - sharpRho) ≤
        65 * (16900 : ℝ) ^ (-(1 / 2 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [sharpRho_bounds.1])
    _ = 1 / 2 := by rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, hroot]; norm_num

/-- The reference normalized by the stage length contracts. The lower bound on the number
of appended terms uses the exact sharp exponent identity. -/
theorem normalized_reference_le {N r C N' B B' : ℝ} (hN : 0 < N) (hC : 0 < C)
    (hB : 0 ≤ B) (hB'₀ : 0 ≤ B') (hr : N ^ sharpS ≤ r)
    (hN' : C * r ^ 2 ≤ N') (hB' : B' ≤ 65 * B * (C * r ^ 2) ^ 2) :
    B' / N' ^ sharpRho ≤ 65 * C ^ (2 - sharpRho) * (B / N ^ sharpRho) := by
  have hr' := (Real.rpow_pos_of_pos hN sharpS).trans_le hr
  have hk : 0 < C * r ^ (2 : ℕ) := by positivity
  have hN'₀ := hk.trans_le hN'
  have hρ : 0 < sharpRho := by linarith [sharpRho_bounds.1]
  have he : 2 - sharpRho ≤ 0 := by linarith [sharpRho_bounds.1]
  have hex : sharpS * (2 * (2 - sharpRho)) = -sharpRho := by
    calc
      sharpS * (2 * (2 - sharpRho)) = -(sharpS * (2 * (sharpRho - 2))) := by ring
      _ = -sharpRho := by rw [sharp_exponent_contract]
  have hrle : r ^ (2 * (2 - sharpRho)) ≤ N ^ (-sharpRho) := by
    have hh := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hN sharpS)
      hr (show 2 * (2 - sharpRho) ≤ 0 by linarith)
    rwa [← Real.rpow_mul hN.le, hex] at hh
  calc
    B' / N' ^ sharpRho ≤ B' / (C * r ^ (2 : ℕ)) ^ sharpRho :=
      div_le_div_of_nonneg_left hB'₀ (Real.rpow_pos_of_pos hk _) (Real.rpow_le_rpow hk.le hN' hρ.le)
    _ ≤ (65 * B * (C * r ^ (2 : ℕ)) ^ 2) / (C * r ^ (2 : ℕ)) ^ sharpRho :=
      div_le_div_of_nonneg_right hB' (Real.rpow_nonneg hk.le _)
    _ = 65 * B * (C * r ^ (2 : ℕ)) ^ (2 - sharpRho) := by
      rw [Real.rpow_sub hk, Real.rpow_ofNat]
      ring
    _ = 65 * B * C ^ (2 - sharpRho) * r ^ (2 * (2 - sharpRho)) := by
      rw [Real.mul_rpow hC.le (sq_nonneg _), ← Real.rpow_natCast r (2 : ℕ), ← Real.rpow_mul hr'.le]
      norm_num
      ring
    _ ≤ 65 * B * C ^ (2 - sharpRho) * N ^ (-sharpRho) :=
      mul_le_mul_of_nonneg_left hrle (by positivity)
    _ = 65 * C ^ (2 - sharpRho) * (B / N ^ sharpRho) := by
      rw [Real.rpow_neg hN.le]
      ring

theorem normalized_reference_contract {N r N' B B' : ℝ} (hN : 0 < N)
    (hB : 0 ≤ B) (hB'₀ : 0 ≤ B') (hr : N ^ sharpS ≤ r)
    (hN' : 16900 * r ^ 2 ≤ N') (hB' : B' ≤ 65 * B * (16900 * r ^ 2) ^ 2) :
    B' / N' ^ sharpRho ≤ (B / N ^ sharpRho) / 2 := by
  have h := normalized_reference_le hN (by norm_num : (0 : ℝ) < 16900) hB hB'₀ hr hN' hB'
  have hmul := mul_le_mul_of_nonneg_right sharp_fixed_factor
    (div_nonneg hB (Real.rpow_nonneg hN.le sharpRho))
  calc
    _ ≤ _ := h.trans hmul
    _ = _ := by ring

/-- Uniform normalized coefficient for the filler and dense-block gap estimates. -/
theorem normalized_gap_coefficients {N r C B g B' : ℝ} (hN : 0 < N)
    (hB : 0 ≤ B) (hr : N ^ sharpS ≤ r) (hr' : r ≤ 2 * N ^ sharpS)
    (hg : g ≤ 17 * B * r) (hB' : B' ≤ 65 * B * C ^ 2 * r ^ 4) :
    6 * g / N ^ gapThreshold + 7 * B' / r ^ (gapThreshold + 1) ≤
      (204 + 455 * C ^ 2) * (B / N ^ sharpRho) := by
  have hr₀ := (Real.rpow_pos_of_pos hN sharpS).trans_le hr
  have hden₁ := Real.rpow_pos_of_pos hN sharpRho
  have hden₂ := Real.rpow_pos_of_pos hr₀ (gapThreshold - 3)
  have hpow₁ : N ^ gapThreshold = N ^ sharpS * N ^ sharpRho := by
    rw [← Real.rpow_add hN, sharp_exponent_gap]
  have hpow₂ : N ^ sharpRho ≤ r ^ (gapThreshold - 3) := by
    have he : 0 ≤ gapThreshold - 3 := by linarith [gapThreshold_eq, sharpS_bounds.1]
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hN.le sharpS) hr he
    rwa [← Real.rpow_mul hN.le, sharp_exponent_filler] at hh
  have h₁ : 6 * g / N ^ gapThreshold ≤ 204 * (B / N ^ sharpRho) := by
    calc
      _ ≤ (6 * (17 * B * (2 * N ^ sharpS))) / N ^ gapThreshold := by
        apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hN.le _)
        exact mul_le_mul_of_nonneg_left
          (hg.trans (mul_le_mul_of_nonneg_left hr' (by positivity))) (by norm_num)
      _ = _ := by
        rw [hpow₁]
        field_simp [(Real.rpow_pos_of_pos hN sharpS).ne', hden₁.ne']
        ring
  have h₂ : 7 * B' / r ^ (gapThreshold + 1) ≤ 455 * C ^ 2 * (B / N ^ sharpRho) := by
    calc
      _ ≤ (7 * (65 * B * C ^ 2 * r ^ 4)) / r ^ (gapThreshold + 1) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hB' (by norm_num))
          (Real.rpow_nonneg hr₀.le _)
      _ = (455 * C ^ 2 * B) / r ^ (gapThreshold - 3) := by
        rw [show gapThreshold + 1 = (4 : ℝ) + (gapThreshold - 3) by ring,
          Real.rpow_add hr₀, Real.rpow_ofNat]
        field_simp [hr₀.ne', hden₂.ne']
        ring
      _ ≤ (455 * C ^ 2 * B) / N ^ sharpRho :=
        div_le_div_of_nonneg_left (by positivity) hden₁ hpow₂
      _ = _ := by ring
  calc
    _ ≤ _ := add_le_add h₁ h₂
    _ = _ := by ring

/-- The consecutive seed has arbitrarily small normalized reference as its length grows. -/
theorem exists_normalized_seed (W : ℝ) (hW : 0 ≤ W) :
    ∃ N : ℕ, 2 ≤ N ∧ W * (((12 * N ^ 2 + N : ℕ) : ℝ) / (N : ℝ) ^ sharpRho) ≤ 1 := by
  obtain ⟨m, hm⟩ := exists_nat_ge (max (2 : ℝ) (13 * W))
  have hm₂ : (2 : ℝ) ≤ (m : ℝ) := (le_max_left _ _).trans hm
  have hmW : 13 * W ≤ (m : ℝ) := (le_max_right _ _).trans hm
  have hmNat : 2 ≤ m := by exact_mod_cast hm₂
  let N := m ^ (2 : ℕ)
  have hmN : m ≤ N := by
    dsimp [N]
    rw [pow_two]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hN₂ := hmNat.trans hmN
  have hN₁ : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr (by omega)
  have hN : (0 : ℝ) < (N : ℝ) := zero_lt_one.trans_le hN₁
  have hpow : (N : ℝ) ^ (5 / 2 : ℝ) = (N : ℝ) ^ (2 : ℕ) * (m : ℝ) := by
    rw [show (5 / 2 : ℝ) = 2 + 1/2 by norm_num, Real.rpow_add hN, Real.rpow_ofNat,
      ← Real.sqrt_eq_rpow]
    congr 1
    dsimp [N]
    rw [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg m)]
  have hsmall : (N : ℝ) ≤ (N : ℝ) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.self_le_rpow_of_one_le hN₁ (by norm_num)
  refine ⟨N, hN₂, ?_⟩
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hN _)).2
  push_cast
  rw [one_mul]
  calc
    W * (12 * (N : ℝ) ^ 2 + (N : ℝ)) ≤ W * (13 * (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hW
    _ = 13 * W * (N : ℝ) ^ 2 := by ring
    _ ≤ (m : ℝ) * (N : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hmW (sq_nonneg _)
    _ = (N : ℝ) ^ (5 / 2 : ℝ) := by rw [hpow, mul_comm]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN₁ sharpRho_bounds.1.le

end Jsp000726.Upper
