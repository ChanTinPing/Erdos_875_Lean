module

public import Jsp000726.LowerEarlyBounds
public import Jsp000726.LowerAsymptoticsBootstrap
public import Jsp000726.LowerGrowth
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

namespace Jsp000726

open Finset Filter

/-- For feasible gap caps, any middle-layer power `u` gives early largest-layer growth
at every power strictly below `u/c`. This is manuscript Lemma 3.1 at integer thresholds. -/
theorem early_largestLayer_of_eventual_gaps {a : ℕ → ℕ} (hmono : StrictMono a)
    (hpos : ∀ n, 0 < a n) (ha : Admissible a) {c u : ℝ} (hc : 0 < c) (hu : 0 < u)
    (huc : u + 1 ≤ c) (hW : PrefixPower (middleLayer a) u)
    (hgap : ∀ᶠ n : ℕ in atTop, (gap a n : ℝ) ≤ ((n : ℝ) + 1) ^ c)
    {v : ℝ} (hv₀ : 0 < v) (hv : v < u / c) : EarlyPower a (largestLayer a) v := by
  obtain ⟨C, hC, hterm⟩ := polynomialTermBound_of_eventual_gaps hmono.monotone hc.le hgap
  have hterm' : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (a n : ℝ) ≤ C * ((n : ℝ) + 1) ^ (c + 1) := by
    refine ⟨C, hC, fun n => ?_⟩
    simpa only [Nat.cast_add, Nat.cast_one] using hterm n
  have hcap := prefixWeightCap_of_termCap (by linarith : 0 ≤ c + 1) hterm'
  have hnext := prefixWeight_succ_le_max_of_eventual_gaps hmono.monotone hc.le hgap
  have hmoment (w : ℝ) (hw₀ : 0 ≤ w) (hw₁ : w < 1) (hE : EarlyPower a (allCounts a) w) :
      EarlyCountMoment a c w := earlyCountMoment_of_early_allCounts hmono hpos hc.le hw₀ hw₁ hgap hE
  exact early_largestLayer_of_uniform_moment ha hpos hu hc huc (by linarith) hW hcap hnext hmoment hv₀ hv

/-- Uniform prefix-weight caps can be written directly in terms of the prefix length. -/
theorem prefixWeightCap_to_pointwise {a : ℕ → ℕ} {b : ℝ} (h : PrefixWeightCap a b) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, (prefixWeight a n : ℝ) ≤ D * (n : ℝ) ^ b := by
  obtain ⟨D, hD, h⟩ := h
  refine ⟨D, hD, fun n => ?_⟩
  cases n with
  | zero =>
      simp only [prefixWeight, range_zero, sum_empty, Nat.cast_zero]
      exact mul_nonneg hD.le (Real.rpow_nonneg le_rfl _)
  | succ n => simpa only [Nat.cast_succ] using h n

/-- A polynomial growth bound on the total count bounds the length of an early prefix. -/
theorem prefixAt_add_one_le_power_of_allCounts {a : ℕ → ℕ} {U : ℝ} (hU : 0 < U)
    (h : PrefixPower (allCounts a) U) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, ((prefixAt a x : ℕ) : ℝ) + 1 ≤ C * ((x : ℝ) + 1) ^ U⁻¹ := by
  obtain ⟨A, hA, h⟩ := h
  refine ⟨A⁻¹ ^ U⁻¹, Real.rpow_pos_of_pos (inv_pos.mpr hA) _, fun x => ?_⟩
  let n := prefixAt a x
  have hN : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hx : (0 : ℝ) ≤ (x : ℝ) + 1 := by positivity
  have hsum : (allCounts a n : ℝ) ≤ (x : ℝ) + 1 := by
    exact_mod_cast le_trans (allCounts_le_prefixWeight_add_one a n) (Nat.succ_le_succ (prefixWeight_at_le a x))
  have hpow : ((n : ℝ) + 1) ^ U ≤ A⁻¹ * ((x : ℝ) + 1) := by
    rw [mul_comm, ← div_eq_mul_inv]
    exact (le_div_iff₀ hA).mpr (by
      rw [mul_comm]
      exact (h n).trans hsum)
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hN _) hpow (inv_nonneg.mpr hU.le)
  rwa [← Real.rpow_mul hN, mul_inv_cancel₀ hU.ne', Real.rpow_one,
    Real.mul_rpow (inv_nonneg.mpr hA.le) hx] at hh

/-- The integer-threshold estimate also works at real thresholds after flooring. -/
theorem earlyPower_real {a Y : ℕ → ℕ} {v : ℝ} (hv : 0 ≤ v) (h : EarlyPower a Y v) :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 1 ≤ x → A * x ^ v ≤ (Y (prefixAt a ⌊x⌋₊) : ℝ) := by
  obtain ⟨A, hA, h⟩ := h
  refine ⟨A / (2 : ℝ) ^ v, div_pos hA (Real.rpow_pos_of_pos (by norm_num) _), fun x hx => ?_⟩
  have hf : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (zero_le_one.trans hx)).mpr (by simpa using hx)
  have hf' : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hf
  have hxf := Nat.lt_floor_add_one x
  have hhalf : x / 2 ≤ (⌊x⌋₊ : ℝ) := by linarith
  calc
    _ = A * (x / 2) ^ v := by
      rw [Real.div_rpow (zero_le_one.trans hx) (by norm_num)]
      ring
    _ ≤ A * (⌊x⌋₊ : ℝ) ^ v :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hhalf hv) hA.le
    _ ≤ _ := h _ hf

end Jsp000726
