module

public import Jsp000726.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726

open Finset Filter

/-- An eventual gap bound at a nonnegative exponent also holds at every index after
adding a constant multiplier. -/
theorem exists_global_gap_cap_of_eventual {a : ℕ → ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hgap : ∀ᶠ n : ℕ in atTop, (gap a n : ℝ) ≤ (n + 1 : ℝ) ^ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (gap a n : ℝ) ≤ C * ((n + 1 : ℕ) : ℝ) ^ c := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hgap
  let C : ℝ := 1 + ∑ j ∈ range N, (gap a j : ℝ)
  have hC : 1 ≤ C := le_add_of_nonneg_right (sum_nonneg fun j _ => Nat.cast_nonneg _)
  refine ⟨C, zero_lt_one.trans_le hC, ?_⟩
  intro n
  let x := ((n + 1 : ℕ) : ℝ)
  have hx : 1 ≤ x := by dsimp [x]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hxpow : 1 ≤ x ^ c := Real.one_le_rpow hx hc
  change (gap a n : ℝ) ≤ C * x ^ c
  by_cases h : N ≤ n
  · have hn : (gap a n : ℝ) ≤ x ^ c := by
      simpa only [x, Nat.cast_add, Nat.cast_one] using hN n h
    exact hn.trans (le_mul_of_one_le_left (by linarith) hC)
  · have hn : n ∈ range N := mem_range.mpr (not_le.mp h)
    have hcap : (gap a n : ℝ) ≤ C :=
      (single_le_sum (f := fun j => (gap a j : ℝ)) (fun j _ => Nat.cast_nonneg _) hn).trans
        (le_add_of_nonneg_left zero_le_one)
    exact hcap.trans (le_mul_of_one_le_right (by linarith) hxpow)

/-- Combining the moment and total-weight estimates yields the real exponent step
(S \ll Z^{2/(1+w)} N^{c(1-w)/(1+w)}). -/
theorem sum_rpow_bound_of_moment_and_weight
    {S A Z N C D c w : ℝ} (hS : 0 < S) (hA : 0 ≤ A) (hZ : 0 ≤ Z)
    (hN : 0 < N) (hC : 0 ≤ C) (hD : 0 ≤ D) (hwl : -1 < w) (hwu : w < 1)
    (hweight : S ≤ C * Z * A ^ (1 - w)) (hmoment : A ^ (2 : ℕ) ≤ D * S * N ^ c) :
    S ≤ (C * D ^ ((1 - w) / 2)) ^ (2 / (1 + w)) *
      Z ^ (2 / (1 + w)) * N ^ (c * (1 - w) / (1 + w)) := by
  let e := (1 - w) / 2
  let α := 2 / (1 + w)
  have he : 0 ≤ e := by dsimp [e]; linarith
  have he' : 0 < 1 - e := by dsimp [e]; linarith
  have hα : 0 ≤ α := div_nonneg (by norm_num) (by linarith)
  have hNpow := Real.rpow_nonneg hN.le c
  have h1 : A ^ (1 - w) ≤ (D * S * N ^ c) ^ e := by
    rw [show 1 - w = (2 : ℝ) * e by dsimp [e]; ring,
      Real.rpow_mul hA 2 e, show A ^ (2 : ℝ) = A ^ (2 : ℕ) from Real.rpow_natCast A 2]
    exact Real.rpow_le_rpow (sq_nonneg A) hmoment he
  let K := C * D ^ e * Z * (N ^ c) ^ e
  have h2 : S ≤ K * S ^ e := by
    calc
      S ≤ C * Z * A ^ (1 - w) := hweight
      _ ≤ C * Z * (D * S * N ^ c) ^ e :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg hC hZ)
      _ = K * S ^ e := by
        dsimp [K]
        rw [Real.mul_rpow (mul_nonneg hD hS.le) hNpow, Real.mul_rpow hD hS.le]
        ring
  have h3 : S ^ (1 - e) ≤ K := by
    apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hS e)).mp
    rw [← Real.rpow_add hS, show e + (1 - e) = 1 by ring, Real.rpow_one, mul_comm]
    exact h2
  have heα : (1 - e) * α = 1 := by
    dsimp [α, e]
    have hn : 1 + w ≠ 0 := by linarith
    field_simp [hn]
    ring
  have hcele : c * e * α = c * (1 - w) / (1 + w) := by
    dsimp [e, α]
    have hn : 1 + w ≠ 0 := by linarith
    field_simp [hn]
  calc
    S = (S ^ (1 - e)) ^ α := by rw [← Real.rpow_mul hS.le, heα, Real.rpow_one]
    _ ≤ K ^ α := Real.rpow_le_rpow (Real.rpow_nonneg hS.le _) h3 hα
    _ = _ := by
      dsimp only [K]
      rw [Real.mul_rpow (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hD _)) hZ)
          (Real.rpow_nonneg hNpow _), Real.mul_rpow (mul_nonneg hC (Real.rpow_nonneg hD _)) hZ,
        ← Real.rpow_mul hNpow, ← Real.rpow_mul hN.le]
      rw [show c * (e * α) = c * (1 - w) / (1 + w) by rw [← mul_assoc, hcele]]

end Jsp000726
