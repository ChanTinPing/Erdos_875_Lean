module

public import Jsp000726.LowerEarlyGrowth

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726

open Finset Filter

/-- An early total-count power bound gives the heavy-terms estimate uniformly for all
prefixes and thresholds at least eight. -/
theorem heavyCount_bound_of_early_allCounts
    {a : ℕ → ℕ} {w : ℝ} (hw : 0 ≤ w) (hEarly : EarlyPower a (allCounts a) w) :
    ∃ C : ℝ, 0 < C ∧ ∀ n H : ℕ, 8 ≤ H →
      (((range n).filter fun i => H ≤ a i).card : ℝ) * (H : ℝ) ^ w ≤ C * (allCounts a n : ℝ) := by
  obtain ⟨A, hA, hBound⟩ := hEarly
  let B := (16 : ℝ) ^ w
  have hB : 0 < B := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨B / A, div_pos hB hA, ?_⟩
  intro n H hH
  let T := ((range n).filter fun i => H ≤ a i)
  have hH₀ : 0 < H := by omega
  have hHdiv : 1 ≤ H / 8 := by omega
  change (T.card : ℝ) * (H : ℝ) ^ w ≤ B / A * (allCounts a n : ℝ)
  by_cases hT : T.Nonempty
  · obtain ⟨i, hi⟩ := hT
    have hiH : H ≤ a i := (mem_filter.mp hi).2
    have hin : i ∈ range n := (mem_filter.mp hi).1
    have hS : H ≤ prefixWeight a n := hiH.trans (single_le_sum (fun j _ => Nat.zero_le (a j)) hin)
    have hprefix : prefixAt a (H / 8) ≤ n := by
      by_contra! hn
      have h' := hS.trans ((prefixWeight_mono a hn.le).trans (prefixWeight_at_le a (H / 8)))
      exact (not_le.mpr (Nat.div_lt_self hH₀ (by decide))) h'
    have hC : (allCounts a (prefixAt a (H / 8)) : ℝ) * (T.card : ℝ) ≤ allCounts a n := by
      have hh := (Nat.mul_le_mul_left (allCounts a (prefixAt a (H / 8))) (Nat.le_succ T.card)).trans
        (earlyCount_mul_heavyCount_le (a := a) hH₀ hprefix)
      exact_mod_cast hh
    have hfloor : H ≤ 16 * (H / 8) := by omega
    have hscale : (H : ℝ) / 16 ≤ ((H / 8 : ℕ) : ℝ) := by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 16)).2
      rw [mul_comm]
      exact_mod_cast hfloor
    have hp : (H : ℝ) ^ w / B ≤ ((H / 8 : ℕ) : ℝ) ^ w := by
      rw [show (H : ℝ) ^ w / B = ((H : ℝ) / 16) ^ w by
        dsimp [B]; rw [Real.div_rpow (Nat.cast_nonneg _) (by norm_num)]]
      exact Real.rpow_le_rpow (by positivity) hscale hw
    have hearly : (A / B) * (H : ℝ) ^ w ≤ allCounts a (prefixAt a (H / 8)) := by
      calc
        _ = A * ((H : ℝ) ^ w / B) := by ring
        _ ≤ A * ((H / 8 : ℕ) : ℝ) ^ w := mul_le_mul_of_nonneg_left hp hA.le
        _ ≤ _ := hBound (H / 8) hHdiv
    have hb : ((T.card : ℝ) * (H : ℝ) ^ w) * (A / B) ≤ allCounts a n := by
      calc
        _ = ((A / B) * (H : ℝ) ^ w) * (T.card : ℝ) := by ring
        _ ≤ (allCounts a (prefixAt a (H / 8)) : ℝ) * (T.card : ℝ) :=
          mul_le_mul_of_nonneg_right hearly (Nat.cast_nonneg _)
        _ ≤ _ := hC
    calc
      (T.card : ℝ) * (H : ℝ) ^ w ≤ (allCounts a n : ℝ) / (A / B) :=
        (le_div_iff₀ (div_pos hA hB)).2 hb
      _ = _ := by field_simp [ne_of_gt hA, ne_of_gt hB]
  · rw [show T = ∅ from not_nonempty_iff_eq_empty.mp hT]
    simp only [card_empty, Nat.cast_zero, zero_mul]
    exact mul_nonneg (div_nonneg hB.le hA.le) (Nat.cast_nonneg _)

end Jsp000726
