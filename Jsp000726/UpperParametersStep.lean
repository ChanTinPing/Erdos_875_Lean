module

public import Jsp000726.UpperParametersNat
public import Jsp000726.UpperParametersGap

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726.Upper

/-- The real bounds for the step size and next reference follow directly from
the integer parameters of the construction. -/
theorem sharp_step_real_bounds {N B C d : ℕ} (hC : 100 ≤ C) (hd : 0 < d)
    (hdr : d ≤ sharpR N) :
    let r := sharpR N
    let K := sharpK r d
    let k := sharpBlock C r
    let R := sharpQ k K
    let g := B * K
    let B' := B + g * R
    (g : ℝ) ≤ 17 * (B : ℝ) * (r : ℝ) ∧
      (B' : ℝ) ≤ 65 * (B : ℝ) * (C : ℝ) ^ 2 * (r : ℝ) ^ 4 := by
  intro r K k R g B'
  have hKBounds : 16 * r < K ∧ K ≤ 17 * r := sharpK_bounds hd hdr
  have hK : 0 < K := (Nat.zero_le _).trans_lt hKBounds.1
  have hKk : 2 * K ≤ k := two_mul_sharpK_le_block hC hd hdr
  have hg : g ≤ 17 * B * r := by
    change B * K ≤ _
    convert Nat.mul_le_mul_left B hKBounds.2 using 1
    ring
  have hB' : B' ≤ 65 * B * k ^ 2 := (sharpReference_bounds hK hKk).2
  constructor
  · exact_mod_cast hg
  · have hle : (B' : ℝ) ≤ 65 * (B : ℝ) * (k : ℝ) ^ 2 := by exact_mod_cast hB'
    have hk : (k : ℝ) = (C : ℝ) * (r : ℝ) ^ 2 := by
      simp only [k, sharpBlock, Nat.cast_mul, Nat.cast_pow]
    rw [hk] at hle
    convert hle using 1
    ring

/-- Contraction for a stage whose new reference is defined by the integer rounding schedule. -/
theorem sharp_step_contract {N B d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (hdr : d ≤ sharpR N) :
    let r := sharpR N
    let K := sharpK r d
    let k := sharpBlock 16900 r
    let R := sharpQ k K
    let B' := B + B * K * R
    let N' := N + r + k
    (B' : ℝ) / (N' : ℝ) ^ sharpRho ≤ ((B : ℝ) / (N : ℝ) ^ sharpRho) / 2 := by
  intro r K k R B' N'
  have hKLower : 16 * r < K := (sharpK_bounds hd hdr).1
  have hK : 0 < K := (Nat.zero_le _).trans_lt hKLower
  have hKk : 2 * K ≤ k := two_mul_sharpK_le_block (by decide) hd hdr
  have hBk : B' ≤ 65 * B * k ^ 2 := (sharpReference_bounds hK hKk).2
  have hBN : (B' : ℝ) ≤ 65 * (B : ℝ) * (k : ℝ) ^ 2 := by exact_mod_cast hBk
  have hkN : (k : ℝ) ≤ (N' : ℝ) := Nat.cast_le.mpr (by dsimp [N']; omega)
  have hk : (k : ℝ) = 16900 * (r : ℝ) ^ 2 := by
    simp only [k, sharpBlock, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [hk] at hBN hkN
  exact normalized_reference_contract (Nat.cast_pos.mpr hN)
    (Nat.cast_nonneg B) (Nat.cast_nonneg B') (rpow_le_sharpR N) hkN hBN

end Jsp000726.Upper
