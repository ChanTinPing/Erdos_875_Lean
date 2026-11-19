module

public import Jsp000726.LowerRankTwoScale

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

@[expose] public section

namespace Jsp000726

open Finset Filter
open scoped Topology

/-- Last prefix of weight at most a real cutoff. -/
noncomputable def realPrefixAt (a : ℕ → ℕ) (H : ℝ) : ℕ := prefixAt a ⌊H⌋₊

theorem prefixWeight_realPrefixAt_le (a : ℕ → ℕ) {H : ℝ} (hH : 0 ≤ H) :
    (prefixWeight a (realPrefixAt a H) : ℝ) ≤ H :=
  prefixWeight_at_floor_le hH

/-- The integer window whose real cutoff is `H` has width `floor H + 1`. -/
theorem prefixWeight_realPrefixAt_lt_window (a : ℕ → ℕ) (H : ℝ) :
    prefixWeight a (realPrefixAt a H) < ⌊H⌋₊ + 1 :=
  Nat.lt_succ_of_le (prefixWeight_at_le _ _)

/-- Strict real separation exceeds the entire corresponding integer cutoff window. -/
theorem nat_window_le_of_real_separation {H : ℝ} {x y : ℕ} (hH : 0 ≤ H)
    (h : (x : ℝ) + H < (y : ℝ)) :
    x + (⌊H⌋₊ + 1) ≤ y := by
  have hh : (x : ℝ) + (⌊H⌋₊ : ℝ) < (y : ℝ) :=
    (add_le_add_right (Nat.floor_le hH) (x : ℝ)).trans_lt h
  have hp : x + ⌊H⌋₊ < y := by exact_mod_cast hh
  exact (show x + (⌊H⌋₊ + 1) = x + ⌊H⌋₊ + 1 by omega) ▸ Nat.succ_le_of_lt hp

/-- The early-layer estimate holds at real cutoffs, including cutoffs below one. -/
theorem earlyPower_largestLayer_real {a : ℕ → ℕ} {v : ℝ} (hv : 0 ≤ v)
    (h : EarlyPower a (largestLayer a) v) :
    ∃ A : ℝ, 0 < A ∧ ∀ H : ℝ, 0 ≤ H →
      A * H ^ v ≤ (largestLayer a (realPrefixAt a H) : ℝ) :=
  earlyPower_real_nonnegative (one_le_largestLayer a) hv h

/-- A real cutoff on any successful large rank-two witness fits in one quarter
of the protected prefix, with a threshold uniform over all witnesses. -/
theorem eventually_four_mul_realPrefixAt_le_protected
    {a : ℕ → ℕ} {B U δ C D E : ℝ} (hB : 0 < B) (hU : 0 < U)
    (hδ : -1 ≤ δ) (hβ : 1 / B ≤ (1 + δ) / U)
    (hexp : (B - 3) * ((1 + δ) / U) - 1 < 0)
    (hC : 0 < C) (hD : 0 < D) (hE : 0 < E) (hZ : PrefixPower (allCounts a) U) :
    ∀ᶠ n : ℕ in atTop, ∀ V M : ℝ, ∀ m : ℕ, ∀ H : ℝ,
      0 < V → 0 < M → 1 ≤ V / M → 0 ≤ H → H ≤ (V / M) ^ (1 + δ) →
      E * V ^ (1 / B) ≤ (m : ℝ) + 1 →
      V ≤ C * ((n : ℝ) + 1) ^ B →
      D * ((n : ℝ) + 1) ^ (3 : ℝ) ≤ M →
      4 * realPrefixAt a H ≤ m := by
  obtain ⟨K, _, hRatio⟩ := rankTwo_real_threshold_support_bound hU hB (by linarith) hβ
    hC hD hE hZ
  let e := (B - 3) * ((1 + δ) / U) - 1
  have he : e < 0 := hexp
  have hcast : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ e) atTop (𝓝 0) := by
    simpa only [neg_neg, Function.comp_def] using
      (tendsto_rpow_neg_atTop (neg_pos.mpr he)).comp hcast
  have hKt : Tendsto (fun n : ℕ => K * ((n : ℝ) + 1) ^ e) atTop (𝓝 0) := by
    simpa only [mul_zero] using ht.const_mul K
  have hevent : ∀ᶠ n : ℕ in atTop, K * ((n : ℝ) + 1) ^ e < 1 / 4 :=
    hKt.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  refine hevent.mono fun n hSmall V M m H hV hM hR hH hHcap hPref hspan hVol => ?_
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have hRat := hRatio hN hV hM hR hH hHcap hPref hspan hVol
  change ((realPrefixAt a H : ℝ) + 1) / ((m : ℝ) + 1) ≤ K * ((n : ℝ) + 1) ^ e at hRat
  have hsmall' := (div_lt_iff₀ (by positivity : 0 < (m : ℝ) + 1)).1 (hRat.trans_lt hSmall)
  have h4 : (4 : ℝ) * (realPrefixAt a H : ℝ) ≤ (m : ℝ) := by linarith
  exact_mod_cast h4

end Jsp000726
