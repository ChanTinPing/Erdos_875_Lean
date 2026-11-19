module

public import Jsp000726.LowerEarly
public import Jsp000726.LowerRankTwoPowers
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726

open Finset Filter
open scoped Topology

/-- The prefix at a real threshold has weight at most the threshold. -/
theorem prefixWeight_at_floor_le {a : ℕ → ℕ} {X : ℝ} (hX : 0 ≤ X) :
    (prefixWeight a (prefixAt a ⌊X⌋₊) : ℝ) ≤ X :=
  (Nat.cast_le.mpr (prefixWeight_at_le a _)).trans (Nat.floor_le hX)

theorem one_le_largestLayer (a : ℕ → ℕ) (n : ℕ) : 1 ≤ largestLayer a n := by
  have hx : 0 ∈ sumLayer a (range n) 0 := mem_sumLayer.mpr ⟨∅, empty_subset _, rfl, sum_empty⟩
  exact (card_pos.mpr ⟨_, hx⟩).trans_le (card_sumLayer_le_largestLayer a (Nat.zero_le _))

/-- The early-layer estimate at nonnegative real thresholds, including the bounded range. -/
theorem earlyPower_real_nonnegative {a Y : ℕ → ℕ} (hY : ∀ n, 1 ≤ Y n)
    {v : ℝ} (hv : 0 ≤ v) (h : EarlyPower a Y v) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 0 ≤ x → K * x ^ v ≤ (Y (prefixAt a ⌊x⌋₊) : ℝ) := by
  obtain ⟨D, hD, h⟩ := earlyPower_real hv h
  refine ⟨min 1 D, lt_min zero_lt_one hD, fun x hx => ?_⟩
  by_cases h₁ : 1 ≤ x
  · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg hx _)).trans (h x h₁)
  · calc
      _ ≤ 1 * x ^ v := mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg hx _)
      _ ≤ 1 := by rw [one_mul]; exact Real.rpow_le_one hx (le_of_not_ge h₁) hv
      _ ≤ _ := by exact_mod_cast hY (prefixAt a ⌊x⌋₊)

/-- The early cutoff uses a sublinear fraction of the protected prefix. The
quantity bounded is `(t+1)/(m+1)`, so rounding causes no extra cases. -/
theorem rankTwo_real_threshold_support_bound {a : ℕ → ℕ} {U B δ C D E : ℝ}
    (hU : 0 < U) (hB : 0 < B) (hδ : 0 ≤ 1 + δ) (hβ : 1 / B ≤ (1 + δ) / U)
    (hC : 0 < C) (hD : 0 < D) (hE : 0 < E) (hZ : PrefixPower (allCounts a) U) :
    ∃ K : ℝ, 0 < K ∧ ∀ {N V M X : ℝ} {m : ℕ},
      0 < N → 0 < V → 0 < M → 1 ≤ V / M → 0 ≤ X → X ≤ (V / M) ^ (1 + δ) →
      E * V ^ (1 / B) ≤ (m : ℝ) + 1 → V ≤ C * N ^ B → D * N ^ (3 : ℝ) ≤ M →
      (((prefixAt a ⌊X⌋₊ : ℕ) : ℝ) + 1) / ((m : ℝ) + 1) ≤ K * N ^ ((B - 3) * ((1 + δ) / U) - 1) := by
  obtain ⟨A, hA, hcount⟩ := hZ
  let β := (1 + δ) / U
  let γ := β - 1 / B
  let K := ((2 / A) ^ (1 / U) / E) * (C ^ γ / D ^ β)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro N V M X m hN hV hM hR hX hcut hm hspan hvolume
  let t := prefixAt a ⌊X⌋₊
  have hS : (prefixWeight a t : ℝ) ≤ X := prefixWeight_at_floor_le hX
  have hC' : (allCounts a t : ℝ) ≤ (prefixWeight a t : ℝ) + 1 := by
    exact_mod_cast allCounts_le_prefixWeight_add_one a t
  have hcount' : A * ((t : ℝ) + 1) ^ U ≤ X + 1 := (hcount t).trans (hC'.trans (add_le_add_left hS 1))
  have hRpower : 1 ≤ (V / M) ^ (1 + δ) := Real.one_le_rpow hR hδ
  have htail : ((t : ℝ) + 1) ^ U ≤ (2 / A) * (V / M) ^ (1 + δ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hA, mul_comm (((t : ℝ) + 1) ^ U)]
    exact hcount'.trans (by linarith)
  exact rankTwo_protected_prefix_ratio_le hN hV hM (by positivity) hB hU hβ (by positivity)
    hC hD hE htail hm hspan hvolume

/-- Along actual prefixes, a negative exponent in the support ratio eventually
leaves at least half of the protected prefix available for padding. -/
theorem eventually_rankTwo_real_threshold_le_half {a : ℕ → ℕ} {U B δ C D E : ℝ}
    (hU : 0 < U) (hB : 0 < B) (hδ : 0 ≤ 1 + δ) (hβ : 1 / B ≤ (1 + δ) / U)
    (hC : 0 < C) (hD : 0 < D) (hE : 0 < E) (hZ : PrefixPower (allCounts a) U)
    (hexp : (B - 3) * ((1 + δ) / U) - 1 < 0) :
    ∀ᶠ n : ℕ in atTop, ∀ {V M X : ℝ} {m : ℕ},
      0 < V → 0 < M → 1 ≤ V / M → 0 ≤ X → X ≤ (V / M) ^ (1 + δ) →
      E * V ^ (1 / B) ≤ (m : ℝ) + 1 → V ≤ C * ((n : ℝ) + 1) ^ B →
      D * ((n : ℝ) + 1) ^ (3 : ℝ) ≤ M → 2 * prefixAt a ⌊X⌋₊ ≤ m := by
  obtain ⟨K, hK, hratio⟩ := rankTwo_real_threshold_support_bound hU hB hδ hβ hC hD hE hZ
  let e := (B - 3) * ((1 + δ) / U) - 1
  have hN : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    refine tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ)) ?_ tendsto_natCast_atTop_atTop
    intro n
    exact le_add_of_nonneg_right zero_le_one
  have hpow : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ e) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (y := -e) (by linarith : 0 < -e)).comp hN
    change Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (- -e)) atTop (𝓝 0) at h
    rwa [neg_neg] at h
  have hKpow : Tendsto (fun n : ℕ => K * ((n : ℝ) + 1) ^ e) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hpow (f := fun _ : ℕ => K)
  have hsmall : ∀ᶠ n : ℕ in atTop, K * ((n : ℝ) + 1) ^ e < (1 / 4 : ℝ) :=
    hKpow.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hsmall] with n hsmall V M X m hV hM hR hX hcut hm hspan hvol
  have h := (hratio (by positivity : 0 < (n : ℝ) + 1) hV hM hR hX hcut hm hspan hvol).trans_lt hsmall
  have h' := (div_lt_iff₀ (by positivity : 0 < (m : ℝ) + 1)).mp h
  let t := prefixAt a ⌊X⌋₊
  have hcast : 4 * ((t : ℝ) + 1) ≤ (m : ℝ) + 1 := by
    dsimp [t]
    linarith
  have hnat : 4 * (t + 1) ≤ m + 1 := by exact_mod_cast hcast
  omega

end Jsp000726
