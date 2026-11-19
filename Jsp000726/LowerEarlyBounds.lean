module

public import Jsp000726.LowerEarlyIteration

@[expose] public section

namespace Jsp000726

open Finset Filter

theorem one_le_middleLayer {a : ℕ → ℕ} (hmono : StrictMono a) (n : ℕ) : 1 ≤ middleLayer a n :=
  (Nat.le_add_right 1 _).trans (card_sumLayer_ge hmono (Nat.div_le_self n 2))

/-- Every increasing sequence supplies the starting exponent two for the middle layer. -/
theorem prefixPower_middleLayer_two {a : ℕ → ℕ} (hmono : StrictMono a) :
    PrefixPower (middleLayer a) 2 := by
  refine ⟨1 / 16, by norm_num, fun n => ?_⟩
  rw [show (((n : ℝ) + 1) ^ (2 : ℝ)) = ((n : ℝ) + 1) ^ (2 : ℕ) by norm_num]
  by_cases hn : 2 ≤ n
  · have h1 : n + 1 ≤ 4 * (n / 2) := by omega
    have h2 : n + 1 ≤ 4 * (n - n / 2) := by omega
    have hc1 : (n : ℝ) + 1 ≤ 4 * ((n / 2 : ℕ) : ℝ) := by exact_mod_cast h1
    have hc2 : (n : ℝ) + 1 ≤ 4 * ((n - n / 2 : ℕ) : ℝ) := by exact_mod_cast h2
    have hprod := mul_le_mul hc1 hc2 (show 0 ≤ (n : ℝ) + 1 by positivity)
      (show 0 ≤ 4 * ((n / 2 : ℕ) : ℝ) by positivity)
    have hcard : 1 + ((n / 2 : ℕ) : ℝ) * ((n - n / 2 : ℕ) : ℝ) ≤ (middleLayer a n : ℝ) := by
      exact_mod_cast card_sumLayer_ge hmono (Nat.div_le_self n 2)
    nlinarith only [hprod, hcard]
  · have hn' : n ≤ 1 := by omega
    have hc : (n : ℝ) + 1 ≤ 2 := by exact_mod_cast (show n + 1 ≤ 2 by omega)
    have hprod := mul_le_mul hc hc (show 0 ≤ (n : ℝ) + 1 by positivity) (show (0 : ℝ) ≤ 2 by norm_num)
    have hcard : (1 : ℝ) ≤ (middleLayer a n : ℝ) := by exact_mod_cast one_le_middleLayer hmono n
    nlinarith only [hprod, hcard]

/-- Extend an eventual lower bound to all prefixes when the counts are always positive. -/
theorem prefixPower_of_eventually {Y : ℕ → ℕ} (hY : ∀ n, 1 ≤ Y n) {u A : ℝ}
    (hu : 0 ≤ u) (hA : 0 < A) (h : ∀ᶠ n : ℕ in atTop, A * ((n : ℝ) + 1) ^ u ≤ (Y n : ℝ)) :
    PrefixPower Y u := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  let B : ℝ := min A ((((N : ℝ) + 1) ^ u)⁻¹)
  have hNp : 0 < (N : ℝ) + 1 := by positivity
  have hpos : 0 < B := lt_min hA (inv_pos.mpr (Real.rpow_pos_of_pos hNp _))
  refine ⟨B, hpos, fun n => ?_⟩
  by_cases hn : N ≤ n
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg (by positivity) _)).trans (hN n hn)
  · have hp : ((n : ℝ) + 1) ^ u ≤ ((N : ℝ) + 1) ^ u := by
      apply Real.rpow_le_rpow (by positivity) _ hu
      have hle : n + 1 ≤ N + 1 := by omega
      exact_mod_cast hle
    have h1 : B * ((n : ℝ) + 1) ^ u ≤ 1 := by
      calc
        _ ≤ ((((N : ℝ) + 1) ^ u)⁻¹) * (((N : ℝ) + 1) ^ u) :=
          mul_le_mul (min_le_right _ _) hp (Real.rpow_nonneg (by positivity) _) (inv_nonneg.mpr (Real.rpow_nonneg hNp.le _))
        _ = 1 := inv_mul_cancel₀ (Real.rpow_pos_of_pos hNp _).ne'
    exact h1.trans (by exact_mod_cast hY n)

/-- A polynomial term cap yields a prefix-weight cap with exponent increased by one. -/
theorem prefixWeightCap_of_termCap {a : ℕ → ℕ} {p : ℝ} (hp : 0 ≤ p)
    (h : ∃ D : ℝ, 0 < D ∧ ∀ i : ℕ, (a i : ℝ) ≤ D * ((i : ℝ) + 1) ^ p) :
    PrefixWeightCap a (p + 1) := by
  obtain ⟨D, hD, h⟩ := h
  refine ⟨D, hD, fun n => ?_⟩
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hh : (∑ i ∈ range (n + 1), (a i : ℝ)) ≤ ∑ _i ∈ range (n + 1), D * ((n : ℝ) + 1) ^ p := by
    refine sum_le_sum fun i hi => (h i).trans (mul_le_mul_of_nonneg_left ?_ hD.le)
    have hle : i + 1 ≤ n + 1 := Nat.succ_le_succ (Nat.lt_succ_iff.mp (mem_range.mp hi))
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hle) hp
  rw [prefixWeight, Nat.cast_sum]
  refine hh.trans_eq ?_
  rw [sum_const, nsmul_eq_mul, card_range, Nat.cast_add, Nat.cast_one, Real.rpow_add hn, Real.rpow_one]
  ring

end Jsp000726
