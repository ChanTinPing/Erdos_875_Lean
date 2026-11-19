module

public import Jsp000726.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

@[expose] public section

namespace Jsp000726

open Filter

/-- All-index polynomial control of the sequence terms with a positive constant. -/
def PolynomialTermBound (a : ℕ → ℕ) (p : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n, (a n : ℝ) ≤ C * ((n + 1 : ℕ) : ℝ) ^ p

theorem EventualGapExponent.mono {c d : ℝ} (hc : EventualGapExponent c) (hcd : c ≤ d) :
    EventualGapExponent d := by
  obtain ⟨a, hmono, hpos, hadm, hgap⟩ := hc
  refine ⟨a, hmono, hpos, hadm, hgap.mono ?_⟩
  intro n hn
  exact hn.trans (Real.rpow_le_rpow_of_exponent_le
    (le_add_of_nonneg_left (Nat.cast_nonneg n)) hcd)

/-- Summing eventual gaps bounded by a nonnegative power gives term exponent `c + 1`. -/
theorem polynomialTermBound_of_eventual_gaps {a : ℕ → ℕ} (ha : Monotone a)
    {c : ℝ} (hc : 0 ≤ c)
    (hgap : ∀ᶠ n : ℕ in atTop, (gap a n : ℝ) ≤ (n + 1 : ℝ) ^ c) :
    PolynomialTermBound a (c + 1) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hgap
  have haux k : (a (N + k) : ℝ) ≤ a N + (k : ℝ) * ((N + k + 1 : ℕ) : ℝ) ^ c := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hk : N ≤ N + k := Nat.le_add_right _ _
      have hmonoPower : ((N + k + 1 : ℕ) : ℝ) ^ c ≤ ((N + (k + 1) + 1 : ℕ) : ℝ) ^ c :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (by omega :
          N + k + 1 ≤ N + (k + 1) + 1)) hc
      have hd : (gap a (N + k) : ℝ) ≤ ((N + k + 1 : ℕ) : ℝ) ^ c := by
        simpa only [Nat.cast_add, Nat.cast_one] using hN (N + k) hk
      have hsum : (a (N + (k + 1)) : ℝ) = a (N + k) + (gap a (N + k) : ℝ) := by
        rw [show N + (k + 1) = N + k + 1 by omega, ← Nat.cast_add, gap]
        rw [Nat.add_sub_of_le (ha (Nat.le_succ _))]
      calc
        (a (N + (k + 1)) : ℝ) = a (N + k) + (gap a (N + k) : ℝ) := hsum
        _ ≤ (a N + (k : ℝ) * ((N + k + 1 : ℕ) : ℝ) ^ c) +
              ((N + k + 1 : ℕ) : ℝ) ^ c := add_le_add ih hd
        _ = a N + ((k + 1 : ℕ) : ℝ) * ((N + k + 1 : ℕ) : ℝ) ^ c := by
          simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_assoc]
        _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left hmonoPower (Nat.cast_nonneg _)) _
  refine ⟨(a N : ℝ) + 1, by positivity, fun n => ?_⟩
  let x : ℝ := ((n + 1 : ℕ) : ℝ)
  have hx : 1 ≤ x := by dsimp [x]; exact_mod_cast (by omega : 1 ≤ n + 1)
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hxpow : 1 ≤ x ^ (c + 1) := Real.one_le_rpow hx (by linarith)
  have hconst : (a N : ℝ) ≤ (a N : ℝ) * x ^ (c + 1) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hxpow (Nat.cast_nonneg (a N))
  change (a n : ℝ) ≤ ((a N : ℝ) + 1) * x ^ (c + 1)
  rw [add_mul, one_mul]
  by_cases hn : N ≤ n
  · let k := n - N
    have hnk : N + k = n := Nat.add_sub_of_le hn
    have hsmall : (k : ℝ) ≤ x := by
      dsimp [x]; exact_mod_cast (by dsimp [k]; omega : k ≤ n + 1)
    have ht := haux k
    rw [hnk] at ht
    change (a n : ℝ) ≤ (a N : ℝ) + (k : ℝ) * x ^ c at ht
    refine ht.trans (add_le_add hconst ?_)
    rw [Real.rpow_add hxpos, Real.rpow_one, mul_comm (x ^ c) x]
    exact mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hxpos.le _)
  · exact (Nat.cast_le.mpr (ha (Nat.le_of_not_ge hn))).trans
      (hconst.trans (le_add_of_nonneg_right (Real.rpow_nonneg hxpos.le _)))

end Jsp000726
