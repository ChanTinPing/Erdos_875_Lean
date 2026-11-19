module

public import Jsp000726.LowerRankOnePrefix
public import Jsp000726.LowerRankTwoPacking
public import Mathlib.Order.Interval.Finset.Nat

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726

open Finset

/-- The span of a translated integer carrier in a fixed-cardinality layer is at
most the total weight of the containing prefix. -/
theorem integer_layer_span_le_prefixWeight {a : ℕ → ℕ} {T : Finset ℕ} {n r : ℕ}
    (hT : T ⊆ range n) {P : Finset ℤ} {lo hi z : ℤ} (hlo : lo ∈ P) (hhi : hi ∈ P)
    (hP : ∀ x ∈ P, z + x ∈ (sumLayer a T r).map Nat.castEmbedding) :
    (hi - lo).toNat ≤ prefixWeight a n := by
  obtain ⟨l, hl, hleft⟩ := mem_map.mp (hP lo hlo)
  obtain ⟨j, hj, hright⟩ := mem_map.mp (hP hi hhi)
  obtain ⟨U, hU, _, hs⟩ := mem_sumLayer.mp hj
  have hsum : j ≤ prefixWeight a n := hs ▸ sum_le_sum_of_subset (hU.trans hT)
  change (l : ℤ) = z + lo at hleft
  change (j : ℤ) = z + hi at hright
  omega

/-- Choose the rank-two protected prefix at half the progression's span. The
rounding is covered uniformly, including diameters zero and one. -/
theorem exists_rankTwo_protected_prefix {a : ℕ → ℕ} (hpos : ∀ i, 0 < a i)
    {C B : ℝ} (hC : 0 < C) (hB : 0 < B)
    (hpref : ∀ j : ℕ, (prefixWeight a j : ℝ) ≤ C * (j : ℝ) ^ B) :
    ∃ E : ℝ, 0 < E ∧ ∀ {n V : ℕ}, (V : ℝ) ≤ C * (n : ℝ) ^ B →
      ∃ m ≤ n / 4, 2 * prefixWeight a m ≤ V ∧ E * (V : ℝ) ^ (1 / B) ≤ (m : ℝ) + 1 := by
  let A := (1 / 4 : ℝ) ^ (1 / B) / (4 * C ^ (1 / B))
  let E := min 1 A
  have hA : 0 < A := by dsimp [A]; positivity
  have hE : 0 < E := lt_min zero_lt_one hA
  refine ⟨E, hE, ?_⟩
  intro n V hV
  by_cases hv : 2 ≤ V
  · have hhalf : (↑(V / 2 : ℕ) : ℝ) ≤ C * (n : ℝ) ^ B :=
      (Nat.cast_le.mpr (Nat.div_le_self V 2)).trans hV
    obtain ⟨m, hm, hS, hratio⟩ := exists_protected_prefix_of_span hpos hC hB hpref hhalf
    refine ⟨m, hm, by omega, ?_⟩
    have hquarter : (V : ℝ) ≤ 4 * (↑(V / 2 : ℕ) : ℝ) := by
      exact_mod_cast (show V ≤ 4 * (V / 2) by omega)
    have hq : (1 / 4 : ℝ) * V ≤ (↑(V / 2 : ℕ) : ℝ) := by linarith
    have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (1 / 4 : ℝ) * V) hq (one_div_nonneg.mpr hB.le)
    rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg V)] at hpow
    calc
      _ ≤ A * (V : ℝ) ^ (1 / B) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg (Nat.cast_nonneg V) _)
      _ = ((1 / 4 : ℝ) ^ (1 / B) * (V : ℝ) ^ (1 / B)) / (4 * C ^ (1 / B)) := by
        dsimp [A]
        ring
      _ ≤ (↑(V / 2 : ℕ) : ℝ) ^ (1 / B) / (4 * C ^ (1 / B)) := div_le_div_of_nonneg_right hpow (by positivity)
      _ ≤ _ := hratio
  · refine ⟨0, Nat.zero_le _, by simp [prefixWeight], ?_⟩
    have hv₁ : (V : ℝ) ≤ 1 := by exact_mod_cast (show V ≤ 1 by omega)
    have hpow : (V : ℝ) ^ (1 / B) ≤ 1 := Real.rpow_le_one (Nat.cast_nonneg V) hv₁ (one_div_nonneg.mpr hB.le)
    calc
      _ ≤ 1 * 1 := mul_le_mul (min_le_left _ _) hpow (Real.rpow_nonneg (Nat.cast_nonneg V) _) zero_le_one
      _ = _ := by simp

/-- The original carrier and its protected-prefix padding yield the two basic
packing inequalities used to force average spacing to infinity. -/
theorem rankTwo_initial_packing {a : ℕ → ℕ} (ha : Admissible a)
    {P T : Finset ℕ} {b q V m : ℕ} (hdis : Disjoint T (range m))
    (hP : P ⊆ sumLayer a T q) (hspan : ∀ x ∈ P, b ≤ x ∧ x ≤ b + V)
    (hm : prefixWeight a m ≤ V) : P.card ≤ V + 1 ∧ (m + 1) * P.card ≤ 2 * V + 1 := by
  constructor
  · have hS : P ⊆ Finset.Icc b (b + V) := fun x hx => mem_Icc.mpr (hspan x hx)
    have hcard := card_le_card hS
    rw [Nat.card_Icc] at hcard
    omega
  · have hp := card_mul_succ_le_span_of_layer ha hdis hP hspan hm
    rw [card_range, mul_comm] at hp
    omega

end Jsp000726
