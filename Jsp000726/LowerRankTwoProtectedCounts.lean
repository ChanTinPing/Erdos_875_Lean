module

public import Jsp000726.LowerRankTwoCountGain
public import Jsp000726.LowerRankTwoPacking

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726

open Finset PublicStructure

/-- Pad an inflated layer by one set of each possible cardinality from the
unused protected prefix to obtain the first rank-two count. -/
theorem rankTwoCountBounds_of_inflated_family {a : ℕ → ℕ} (ha : Admissible a)
    {n m t b W V r : ℕ} {P : IntegerGAP} {X L : Finset ℕ} {c v A E : ℝ}
    (hM : 0 < P.carrier.card) (hV : 0 < V) (ht : 2 * t ≤ m)
    (hdis : Disjoint L (range m)) (hX : X ⊆ sumLayer a (range t ∪ L) r)
    (hspan : ∀ x ∈ X, b ≤ x ∧ x ≤ b + W)
    (hW : W ≤ V + prefixWeight a m) (hmBudget : 2 * prefixWeight a m ≤ V)
    (hm : A * (V : ℝ) ^ (1 / (c + 2)) ≤ (m : ℝ) + 1)
    (hcount : E * (P.carrier.card : ℝ) * ((V : ℝ) / (P.carrier.card : ℝ)) ^ rankTwoSigma c v ≤
      (X.card : ℝ))
    (hPadding : X.card ≤ middleLayer a n) :
    RankTwoCountBounds a n P c v A (E / 6) E := by
  let S := range m \ range t
  have ht' : t ≤ m := by omega
  have hIm : range t ⊆ range m := range_subset_range.mpr ht'
  have hDis : Disjoint (range t ∪ L) S := by
    apply disjoint_left.mpr
    intro i hi hiS
    obtain ⟨him, hit⟩ := mem_sdiff.mp hiS
    rcases mem_union.mp hi with hi | hi
    · exact hit hi
    · exact disjoint_left.mp hdis hi him
  have hBudget : (∑ i ∈ S, a i) ≤ prefixWeight a m :=
    sum_le_sum_of_subset (sdiff_subset (s := range m) (t := range t))
  have hpack := card_mul_succ_le_span_of_layer ha hDis hX hspan hBudget
  have hS : S.card + t = m := by
    simpa only [S, card_range] using card_sdiff_add_card_eq_card hIm
  have hSm : m + 1 ≤ 2 * (S.card + 1) := by omega
  have hRange : W + prefixWeight a m + 1 ≤ 3 * V := by omega
  have htotal : X.card * (m + 1) ≤ 6 * V := calc
    _ ≤ X.card * (2 * (S.card + 1)) := Nat.mul_le_mul_left _ hSm
    _ = 2 * (X.card * (S.card + 1)) := by ring
    _ ≤ 2 * (W + prefixWeight a m + 1) := Nat.mul_le_mul_left _ hpack
    _ ≤ _ := by omega
  let M : ℝ := (P.carrier.card : ℝ)
  let R : ℝ := (V : ℝ) / M
  have hM' : 0 < M := Nat.cast_pos.mpr hM
  have hV' : 0 < (V : ℝ) := by exact_mod_cast hV
  have hR : 0 < R := div_pos hV' hM'
  have heq : R * M = (V : ℝ) := div_mul_cancel₀ _ hM'.ne'
  have htotal' : (X.card : ℝ) * ((m : ℝ) + 1) ≤ 6 * (V : ℝ) := by exact_mod_cast htotal
  refine ⟨R, (m : ℝ) + 1, hR, ?_, ?_, ?_⟩
  · change A * (R * M) ^ (1 / (c + 2)) ≤ (m : ℝ) + 1
    rw [heq]
    exact hm
  · change (E / 6) * ((m : ℝ) + 1) * M * R ^ rankTwoSigma c v ≤ R * M
    rw [heq]
    have hprod := (mul_le_mul_of_nonneg_right hcount (show 0 ≤ (m : ℝ) + 1 by positivity)).trans htotal'
    calc
      _ = (E * M * R ^ rankTwoSigma c v * ((m : ℝ) + 1)) / 6 := by ring
      _ ≤ (6 * (V : ℝ)) / 6 := div_le_div_of_nonneg_right hprod (by norm_num)
      _ = _ := by ring
  · exact hcount.trans (by exact_mod_cast hPadding)

end Jsp000726
