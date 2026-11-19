module

public import Jsp000726.LowerAsymptotics
public import Jsp000726.LowerAsymptoticsPower
public import Jsp000726.LowerEarlyCounts
public import Jsp000726.LowerEarlyAlgebra

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

@[expose] public section

namespace Jsp000726

open Finset Filter

/-- Prefix-length version of the square-moment bound, with a positive normalization
even at the empty prefix. -/
theorem sq_le_mul_prefixWeight_rpow_of_eventual_gaps
    {a : ℕ → ℕ} (ha : Monotone a) {c : ℝ} (hc : 0 ≤ c)
    (hgap : ∀ᶠ n : ℕ in atTop, (gap a n : ℝ) ≤ (n + 1 : ℝ) ^ c) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ,
      (a (n - 1) : ℝ) ^ 2 ≤
        D * (max 1 (prefixWeight a n : ℝ)) * ((n : ℝ) + 1) ^ c := by
  obtain ⟨C, hC, hglobal⟩ := exists_global_gap_cap_of_eventual hc hgap
  let D : ℝ := max (1 + (a 0 : ℝ) ^ 2) (2 * max C (a 0 : ℝ))
  have hD : 0 < D := (by positivity : 0 < 1 + (a 0 : ℝ) ^ (2 : ℕ)).trans_le
    (le_max_left _ _)
  refine ⟨D, hD, ?_⟩
  intro n
  cases n with
  | zero =>
    simp only [Nat.zero_sub, Nat.cast_zero, zero_add, Real.one_rpow, mul_one]
    exact ((le_add_of_nonneg_left zero_le_one).trans (le_max_left _ _)).trans
      (le_mul_of_one_le_right hD.le (le_max_left _ _))
  | succ m =>
    simp only [Nat.succ_sub_one]
    have h := sq_le_mul_sum_rpow_of_gap_cap ha hc hC.le hglobal m
    have hS : (prefixWeight a (m + 1) : ℝ) = ∑ i ∈ range (m + 1), (a i : ℝ) := by
      simp only [prefixWeight, Nat.cast_sum]
    rw [← hS] at h
    have hcoeff : (2 * max C (a 0 : ℝ)) * (prefixWeight a (m + 1) : ℝ) ≤
        D * max 1 (prefixWeight a (m + 1) : ℝ) :=
      mul_le_mul (le_max_right _ _) (le_max_right _ _) (Nat.cast_nonneg _) hD.le
    have hpow : ((m + 1 : ℕ) : ℝ) ^ c ≤ ((m.succ : ℝ) + 1) ^ c := by
      refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ hc
      exact le_add_of_nonneg_right zero_le_one
    exact h.trans (mul_le_mul hcoeff hpow (by positivity) (by positivity))

/-- Taking one additional term enlarges the prefix weight by at most a fixed
multiple of its current weight and the current gap scale. -/
theorem prefixWeight_succ_le_max_of_eventual_gaps
    {a : ℕ → ℕ} (ha : Monotone a) {c : ℝ} (hc : 0 ≤ c)
    (hgap : ∀ᶠ n : ℕ in atTop, (gap a n : ℝ) ≤ (n + 1 : ℝ) ^ c) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, (prefixWeight a (n + 1) : ℝ) ≤
      D * max (max 1 (prefixWeight a n : ℝ)) (((n : ℝ) + 1) ^ c) := by
  obtain ⟨C, hC, hglobal⟩ := exists_global_gap_cap_of_eventual hc hgap
  let D := (a 0 : ℝ) + 2 + C
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro n
  let X : ℝ := ((n : ℝ) + 1) ^ c
  let Z : ℝ := max (max 1 (prefixWeight a n : ℝ)) X
  have hZ₁ : 1 ≤ Z := (le_max_left _ _).trans (le_max_left _ _)
  have hZX : X ≤ Z := le_max_right _ _
  have hZS : (prefixWeight a n : ℝ) ≤ Z := (le_max_right _ _).trans (le_max_left _ _)
  change (prefixWeight a (n + 1) : ℝ) ≤ D * Z
  cases n with
  | zero =>
    have hp : prefixWeight a 1 = a 0 := by simp [prefixWeight]
    rw [hp]
    exact (show (a 0 : ℝ) ≤ D by dsimp [D]; linarith).trans
      (le_mul_of_one_le_right hD.le hZ₁)
  | succ m =>
    have haPrev : (a m : ℝ) ≤ (prefixWeight a (m + 1) : ℝ) := by
      simp only [prefixWeight, Nat.cast_sum]
      exact single_le_sum (f := fun i => (a i : ℝ)) (fun i _ => Nat.cast_nonneg _)
        (mem_range.mpr (Nat.lt_succ_self _))
    have hinc : (a (m + 1) : ℝ) = (a m : ℝ) + (gap a m : ℝ) := by
      rw [gap, Nat.cast_sub (ha (Nat.le_succ _))]
      ring
    have hp : ((m + 1 : ℕ) : ℝ) ^ c ≤ X := by
      refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ hc
      exact le_add_of_nonneg_right zero_le_one
    have hgap' := (hglobal m).trans (mul_le_mul_of_nonneg_left (hp.trans hZX) hC.le)
    have hLast := haPrev.trans hZS
    calc
      (prefixWeight a (m.succ + 1) : ℝ) = (prefixWeight a (m + 1) : ℝ) +
          (a m : ℝ) + (gap a m : ℝ) := by
        rw [prefixWeight_succ, Nat.cast_add, hinc]
        ring
      _ ≤ Z + Z + C * Z := add_le_add (add_le_add hZS hLast) hgap'
      _ = (2 + C) * Z := by ring
      _ ≤ D * Z := mul_le_mul_of_nonneg_right
        (by dsimp [D]; linarith [Nat.cast_nonneg (α := ℝ) (a 0)]) (by linarith)

/-- The heavy-terms bound and gap cap give the prefix moment estimate in Lemma 3.1,
with the positive normalization also valid at the empty prefix. -/
theorem prefixWeight_moment_bound_of_tail_and_gaps
    {a : ℕ → ℕ} (ha : Monotone a) (hapos : ∀ n, 0 < a n)
    {c w C : ℝ} (hc : 0 ≤ c) (hw₀ : 0 ≤ w) (hw₁ : w < 1) (hC : 0 ≤ C)
    (hgap : ∀ᶠ n : ℕ in atTop, (gap a n : ℝ) ≤ (n + 1 : ℝ) ^ c)
    (Z : ℕ → ℝ) (hZ : ∀ n : ℕ, max 1 (n : ℝ) ≤ Z n)
    (H₀ : ℕ)
    (htail : ∀ n H : ℕ, 0 < H → H₀ ≤ H →
      (((range n).filter fun i => H ≤ a i).card : ℝ) * (H : ℝ) ^ w ≤ C * Z n) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, (max 1 (prefixWeight a n : ℝ)) ^ ((1 + w) / 2) ≤
      K * Z n * ((n : ℝ) + 1) ^ (c * ((1 - w) / 2)) := by
  obtain ⟨D, hD, hmoment⟩ := sq_le_mul_prefixWeight_rpow_of_eventual_gaps ha hc hgap
  let q := (2 : ℝ) ^ (1 - w)
  let B := (2 * q / (q - 1)) * max C ((H₀ : ℝ) ^ w)
  let J := max 1 B * D ^ ((1 - w) / 2)
  let K := max 1 J
  have hB : 0 < max 1 B := zero_lt_one.trans_le (le_max_left _ _)
  have hK : 1 ≤ K := le_max_left _ _
  refine ⟨K, zero_lt_one.trans_le hK, ?_⟩
  intro n
  have hZ₁ : 1 ≤ Z n := (le_max_left _ _).trans (hZ _)
  have hZ₀ : 0 ≤ Z n := zero_le_one.trans hZ₁
  have hN₀ : 0 ≤ (n : ℝ) + 1 := by positivity
  cases n with
  | zero =>
    simp only [prefixWeight, range_zero, sum_empty, Nat.cast_zero, max_eq_left zero_le_one,
      zero_add, Real.one_rpow, mul_one]
    exact hK.trans (le_mul_of_one_le_right (zero_le_one.trans hK) hZ₁)
  | succ n =>
    have hS : 1 ≤ (prefixWeight a (n + 1) : ℝ) := by
      exact_mod_cast (show 1 ≤ prefixWeight a (n + 1) from
        (hapos n).trans_le (single_le_sum (f := a) (fun _ _ => Nat.zero_le _)
          (mem_range.mpr (Nat.lt_succ_self _))))
    simp only [max_eq_right hS]
    have hsize : ((range (n + 1)).card : ℝ) ≤ Z (n + 1) := by
      rw [card_range]
      exact (le_max_right _ _).trans (hZ _)
    have hweight := sum_weights_le_of_large_tail_count (range (n + 1)) a (hapos n)
      (fun i hi => ha (Nat.lt_succ_iff.mp (mem_range.mp hi))) hw₀ hw₁ hC hsize (htail (n + 1))
    have hmoment' := hmoment (n + 1)
    simp only [Nat.add_sub_cancel, max_eq_right hS] at hmoment'
    have hweight' : (prefixWeight a (n + 1) : ℝ) ≤ max 1 B * Z (n + 1) * (a n : ℝ) ^ (1 - w) := by
      have hh : (prefixWeight a (n + 1) : ℝ) ≤ B * Z (n + 1) * (a n : ℝ) ^ (1 - w) := by
        simpa only [prefixWeight, Nat.cast_sum, B, q] using hweight
      exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hZ₀)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    have h := prefix_moment_of_weight_and_gap (zero_lt_one.trans_le hS)
      (Nat.cast_nonneg (a n)) hZ₀ (by positivity) hB hD hw₁.le hweight' hmoment'
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hZ₀) (Real.rpow_nonneg hN₀ _))

end Jsp000726
