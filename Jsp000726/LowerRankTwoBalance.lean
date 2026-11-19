module

public import Jsp000726.LowerGainChoice

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726

/-- Balance the separated-chain and minimum-spacing bounds, keeping the
constant in the estimate for chain length explicit. -/
theorem rank_two_balance {R L d C μ v δ : ℝ} (hR : 1 ≤ R) (hL : 0 < L) (hd : 0 ≤ d)
    (hC : 1 ≤ C) (hμ : 0 < μ) (hv : 0 < v) (hv₁ : v ≤ 1)
    (hLmajor : L ≤ C * d ^ μ)
    (hsigma : (1 + δ) * v ^ 2 / (μ + v) ≤ v - δ * (1 - v)) :
    R ^ ((1 + δ) * v ^ 2 / (μ + v)) / C ≤
      max (d ^ v) (R ^ v * min L (R ^ δ) ^ v / L) := by
  let σ := (1 + δ) * v ^ 2 / (μ + v)
  change R ^ σ / C ≤ _
  have hR₀ : 0 < R := zero_lt_one.trans_le hR
  have hC₀ : 0 < C := zero_lt_one.trans_le hC
  have hdrop : R ^ σ / C ≤ R ^ σ :=
    div_le_self (Real.rpow_nonneg hR₀.le _) hC
  by_cases hsmall : L ≤ R ^ δ
  · rw [min_eq_left hsmall]
    apply le_max_of_le_right
    calc
      R ^ σ / C ≤ R ^ σ := hdrop
      _ ≤ R ^ (v - δ * (1 - v)) := Real.rpow_le_rpow_of_exponent_le hR hsigma
      _ = R ^ v / (R ^ δ) ^ (1 - v) := by rw [Real.rpow_sub hR₀, Real.rpow_mul hR₀.le]
      _ ≤ R ^ v / L ^ (1 - v) := by
        apply div_le_div_of_nonneg_left (Real.rpow_nonneg hR₀.le _) (Real.rpow_pos_of_pos hL _)
        exact Real.rpow_le_rpow hL.le hsmall (sub_nonneg.mpr hv₁)
      _ = R ^ v * L ^ v / L := by
        rw [Real.rpow_sub hL, Real.rpow_one]
        field_simp [(Real.rpow_pos_of_pos hL v).ne', hL.ne']
  · have hlarge : R ^ δ ≤ L := le_of_not_ge hsmall
    rw [min_eq_right hlarge]
    let α := (1 + δ) * v / (μ + v)
    have hαv : α * v = σ := by dsimp [α, σ]; ring
    by_cases hcut : R ^ α ≤ d
    · apply le_max_of_le_left
      calc
        R ^ σ / C ≤ R ^ σ := hdrop
        _ = (R ^ α) ^ v := by rw [← hαv, Real.rpow_mul hR₀.le]
        _ ≤ d ^ v := Real.rpow_le_rpow (Real.rpow_nonneg hR₀.le _) hcut hv.le
    · apply le_max_of_le_right
      have hL' : L ≤ C * R ^ (α * μ) := by
        apply hLmajor.trans
        rw [Real.rpow_mul hR₀.le]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hd (le_of_not_ge hcut) hμ.le) hC₀.le
      have he : (1 + δ) * v - α * μ = σ := by
        dsimp [α, σ]
        field_simp [ne_of_gt (add_pos hμ hv)]
        ring
      have hprod : R ^ v * (R ^ δ) ^ v = R ^ ((1 + δ) * v) := by
        rw [← Real.rpow_mul hR₀.le, ← Real.rpow_add hR₀]
        congr 1
        ring
      calc
        R ^ σ / C = (R ^ ((1 + δ) * v) / R ^ (α * μ)) / C := by
          rw [← Real.rpow_sub hR₀, he]
        _ = (R ^ ((1 + δ) * v)) / (C * R ^ (α * μ)) := by ring
        _ ≤ (R ^ ((1 + δ) * v)) / L :=
          div_le_div_of_nonneg_left (Real.rpow_nonneg hR₀.le _) hL hL'
        _ = _ := by rw [hprod]

/-- The exponent used in the small-chain case dominates the rank-two target
on the interval needed for the sharp gap theorem. -/
theorem rankTwoSigma_le_small_chain_exponent {c v : ℝ}
    (hc : 4.55 ≤ c) (hc_hi : c ≤ 4.562) (hv : 3 / 5 ≤ v) (hv_hi : v ≤ (c - 1) / c) :
    rankTwoSigma c v ≤ v - (3 / 25) * (1 - v) := by
  have hcpos : 0 < c := by linarith
  have hv₀ : 0 < v := by linarith
  have hv₁ : v < 1 := hv_hi.trans_lt ((div_lt_one hcpos).2 (by linarith))
  have hdiv := (le_div_iff₀ hcpos).1 hv_hi
  have hv_mul : v ≤ (c - 1) * (1 - v) := by nlinarith only [hdiv]
  have hcp : 0 < c + 1 := by linarith
  have hσ : rankTwoSigma c v ≤ ((28 / 25 : ℝ) * (c - 1) / (c + 1)) * v := by
    unfold rankTwoSigma
    rw [div_le_iff₀ (mul_pos hcp (by linarith : 0 < 1 - v))]
    calc
      _ ≤ ((28 / 25 : ℝ) * v) * ((c - 1) * (1 - v)) := by
        simpa only [pow_two, mul_assoc] using
          mul_le_mul_of_nonneg_left hv_mul (by positivity : 0 ≤ (28 / 25 : ℝ) * v)
      _ = _ := by
        field_simp [hcp.ne']
  have hfactor : (28 / 25 : ℝ) * (c - 1) / (c + 1) ≤ 89 / 100 := by
    rw [div_le_iff₀ hcp]
    linarith
  have hs : rankTwoSigma c v ≤ (89 / 100 : ℝ) * v :=
    hσ.trans (mul_le_mul_of_nonneg_right hfactor hv₀.le)
  linarith only [hs, hv]

/-- Rank-two balance in the paper's parameters, for direct use with a protected
chain-length estimate. -/
theorem rank_two_gap_balance {c v R L d C : ℝ} (hc : 4.55 ≤ c) (hc_hi : c ≤ 4.562)
    (hv : 3 / 5 ≤ v) (hv_hi : v ≤ (c - 1) / c)
    (hR : 1 ≤ R) (hL : 0 < L) (hd : 0 ≤ d) (hC : 1 ≤ C)
    (hLmajor : L ≤ C * d ^ gapMu c v) :
    R ^ rankTwoSigma c v / C ≤
      max (d ^ v) (R ^ v * min L (R ^ (3 / 25 : ℝ)) ^ v / L) := by
  have hv₀ : 0 < v := by linarith
  have hv₁ : v ≤ 1 := hv_hi.trans ((div_le_one (by linarith : 0 < c)).2 (by linarith))
  have hσ : (1 + (3 / 25 : ℝ)) * v ^ 2 / (gapMu c v + v) = rankTwoSigma c v := by
    have hden : gapMu c v + v = (c + 1) * (1 - v) := by unfold gapMu; ring
    rw [hden, rankTwoSigma]
    norm_num
  have hh := rank_two_balance hR hL hd hC (gapMu_pos_of_le hc hv_hi) hv₀ hv₁ hLmajor
    (by rw [hσ]; exact rankTwoSigma_le_small_chain_exponent hc hc_hi hv hv_hi)
  rwa [hσ] at hh

end Jsp000726
