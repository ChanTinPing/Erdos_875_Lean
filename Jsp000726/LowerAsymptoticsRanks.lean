module

public import Jsp000726.LowerStructuralBridge
public import Jsp000726.LowerAsymptoticsRankPadding
public import Jsp000726.LowerEarlyBounds

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

@[expose] public section

namespace Jsp000726

open Finset Filter PublicStructure

/-- The structural witness on the opposite pairs at positions
`n / 2` through `n / 2 + 2 * (n / 16)`, with uniform parameter `C`. -/
def OppositeLayerWitness (a : ℕ → ℕ) (n C : ℕ) (P : IntegerGAP) : Prop :=
  let q := n / 2
  let m := n / 16
  P.Proper ∧ (∀ i, m ≤ C * P.length i) ∧ m ^ (P.rank + 1) ≤ C * P.carrier.card ∧
    ∀ x ∈ P.carrier, ((∑ i : Fin m, a (oppositeLow q m i) : ℕ) : ℤ) + x ∈
      (sumLayer a (univ.map (oppositeLow q m) ∪ univ.map (oppositeHigh q m)) m).map
        Nat.castEmbedding

/-- The exact eventual uniform lower bound required of a fixed-rank case. -/
def OppositeRankGain (a : ℕ → ℕ) (C rank : ℕ) (w : ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop,
    ∀ P : IntegerGAP, P.rank = rank → OppositeLayerWitness a n C P →
      A * ((n : ℝ) + 1) ^ w ≤ (middleLayer a n : ℝ)

theorem oppositeRankGain_antitone (a : ℕ → ℕ) (C rank : ℕ) :
    Antitone (OppositeRankGain a C rank) := by
  intro v w hvw
  rintro ⟨A, hA, hgain⟩
  refine ⟨A, hA, hgain.mono ?_⟩
  intro n hn P hR hP
  have hbase : 1 ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hle := Real.rpow_le_rpow_of_exponent_le hbase hvw
  exact (mul_le_mul_of_nonneg_left hle hA.le).trans (hn P hR hP)

private theorem direct_gain_constant_pos {C : ℕ} (hC : 0 < C) (r : ℕ) :
    0 < (((32 : ℝ) ^ (r + 1) * C)⁻¹) := by positivity

/-- High rank pays directly through the number of progression points. -/
theorem opposite_direct_gain {a : ℕ → ℕ} {n C r : ℕ} {P : IntegerGAP} {w : ℝ}
    (hC : 0 < C) (hn : 16 ≤ n) (hR : r ≤ P.rank) (hw : w ≤ ((r + 1 : ℕ) : ℝ))
    (h : OppositeLayerWitness a n C P) :
    (((32 : ℝ) ^ (r + 1) * C)⁻¹) * ((n : ℝ) + 1) ^ w ≤ (middleLayer a n : ℝ) := by
  obtain ⟨_, _, hcard, htrans⟩ := h
  have hdirect := opposite_rank_direct_middleLayer_bound hn hR hcard htrans
  have hle : ((n : ℝ) + 1) ^ w ≤ ((n : ℝ) + 1) ^ (r + 1 : ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_left (Nat.cast_nonneg n)) hw
  have hden : 0 < (32 : ℝ) ^ (r + 1) * C := by positivity
  rw [inv_mul_eq_div]
  apply (div_le_iff₀ hden).2
  rw [mul_comm]
  exact hle.trans hdirect

/-- Rank two yields a cubic bound directly when the target exponent is at most three. -/
theorem oppositeRankGain_two_of_le_three {a : ℕ → ℕ} {C : ℕ} (hC : 0 < C)
    {w : ℝ} (hw : w ≤ 3) : OppositeRankGain a C 2 w := by
  refine ⟨_, direct_gain_constant_pos hC 2, ?_⟩
  filter_upwards [eventually_ge_atTop (16 : ℕ)] with n hn P hr hP
  have hw' : w ≤ ((2 + 1 : ℕ) : ℝ) := by simpa only [Nat.reduceAdd, Nat.cast_ofNat] using hw
  exact opposite_direct_gain (r := 2) hC hn (le_of_eq hr.symm) hw' hP

/-- Merge the uniform rank-one and rank-two estimates with the direct rank-at-least-three
estimate. The lower exponent for a rank-two case can be read from its cardinality alone. -/
theorem prefixPower_middleLayer_of_opposite_branches
    {a : ℕ → ℕ} (ha : StrictMono a) {p w : ℝ} (hp₀ : 0 ≤ p) (hp₆ : p < 6)
    (haPoly : PolynomialTermBound a p) (hstruct : PowerSubsetStructure)
    (hw₀ : 0 ≤ w) (hw₄ : w ≤ 4)
    (h₁ : ∀ C : ℕ, 0 < C → OppositeRankGain a C 1 w)
    (h₂ : 3 < w → ∀ C : ℕ, 0 < C → OppositeRankGain a C 2 w) :
    PrefixPower (middleLayer a) w := by
  obtain ⟨D, C, _, hC, hprogression⟩ :=
    eventually_opposite_layer_structure ha hp₀ hp₆ haPoly hstruct
  obtain ⟨A, hA, hOne⟩ := h₁ C hC
  have hTwo : OppositeRankGain a C 2 w := by
    rcases le_or_gt w 3 with hsmall | hlarge
    · exact oppositeRankGain_two_of_le_three hC hsmall
    · exact h₂ hlarge C hC
  obtain ⟨B, hB, hTwo⟩ := hTwo
  let K := (((32 : ℝ) ^ (3 + 1 : ℕ) * C)⁻¹)
  have hK : 0 < K := direct_gain_constant_pos hC 3
  apply prefixPower_of_eventually (one_le_middleLayer ha) hw₀ (A := min (min A B) K)
    (lt_min (lt_min hA hB) hK)
  filter_upwards [hOne, hTwo, hprogression, eventually_ge_atTop (16 : ℕ)] with n
    hOne hTwo hP hn
  obtain ⟨P, hR, _, hproper, hlen, hcard, htranslated⟩ := hP
  have hwitness : OppositeLayerWitness a n C P := ⟨hproper, hlen, hcard, htranslated⟩
  have hpow : 0 ≤ ((n : ℝ) + 1) ^ w := Real.rpow_nonneg (by positivity) _
  rcases (show P.rank = 1 ∨ P.rank = 2 ∨ 3 ≤ P.rank by omega) with h | h | h
  · exact (mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (min_le_left _ _)) hpow).trans
      (hOne P h hwitness)
  · exact (mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (min_le_right _ _)) hpow).trans
      (hTwo P h hwitness)
  · have hw' : w ≤ ((3 + 1 : ℕ) : ℝ) := by simpa only [Nat.reduceAdd, Nat.cast_ofNat] using hw₄
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hpow).trans
      (opposite_direct_gain (r := 3) hC hn h hw' hwitness)

end Jsp000726
