module

public import Jsp000726.LowerSharpReduction
public import Jsp000726.LowerRankOneStructural

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

@[expose] public section

namespace Jsp000726

open Filter PublicStructure

/-- The remaining rank-two improvement only needs to raise the middle-layer bound
above the direct cubic estimate, and only for the displayed range of exponents. -/
def RefinedRankTwoGain (a : ℕ → ℕ) (c : ℝ) : Prop :=
  ∀ u v w : ℝ, 2.99 ≤ u → u + 1 ≤ c → 3 / 5 < v → v < u / c →
    0 < gapMu c v → 3 < w → w ≤ gapRankTwoGain c v → PrefixPower (middleLayer a) u →
    ∀ C : ℕ, 0 < C → OppositeRankGain a C 2 w

theorem gapRankGain_of_structure_and_refined_rank_two {a : ℕ → ℕ} {c : ℝ}
    (hmono : StrictMono a) (hpos : ∀ n, 0 < a n) (ha : Admissible a)
    (hcl : 4.55 ≤ c) (hcu : c < gapThreshold)
    (hgap : ∀ᶠ n : ℕ in atTop, (gap a n : ℝ) ≤ (n + 1 : ℝ) ^ c)
    (hstructure : PowerSubsetStructure) (h₂ : RefinedRankTwoGain a c) :
    GapRankGain a c := by
  intro u hu hW v hv₀ hv hmu w hw₁ hw₄ hw₂
  have hc : 0 < c := by linarith
  have hcp : 0 ≤ c + 1 := by linarith
  have hcp₆ : c + 1 < 6 := by linarith [hcu.trans gapThreshold_lt_4562]
  have huc : u + 1 ≤ c := by linarith [hu.2]
  have hup : 0 < u := by linarith [hu.1]
  have hp := polynomialTermBound_of_eventual_gaps hmono.monotone hc.le hgap
  rcases le_or_gt 0 w with hw₀ | hw₀
  · apply prefixPower_middleLayer_of_opposite_branches hmono hcp hcp₆ hp hstructure hw₀ hw₄
    · exact oppositeRankGain_one_of_eventual_gaps hmono hpos ha hc hup huc hv₀ hv hmu hw₀ hw₁ hW hgap
    · intro hw₃
      obtain ⟨hu₀, hv₁, hw⟩ := hw₂.resolve_left (not_le.mpr hw₃)
      exact h₂ u v w hu₀ huc hv₁ hv hmu hw₃ hw hW
  · obtain ⟨A, hA, hbase⟩ := prefixPower_middleLayer_two hmono
    refine ⟨A, hA, fun n => ?_⟩
    have hbase₁ : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
    have hle : w ≤ (2 : ℝ) := by linarith
    exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hbase₁ hle) hA.le)
      |>.trans (hbase n)

/-- The sharp gap classification follows from the public structural endpoint and
the explicit refined rank-two branch. The other rank branches and both reductions
to the original statements are proved here. -/
theorem sharpGapStatements_of_dyadic_and_refined_rank_two (hstructure : DyadicSubsetStructure)
    (h₂ : ∀ (a : ℕ → ℕ) (c : ℝ), StrictMono a → (∀ n, 0 < a n) → Admissible a →
      4.55 ≤ c → c < gapThreshold →
      (∀ᶠ n : ℕ in atTop, (gap a n : ℝ) ≤ (n + 1 : ℝ) ^ c) → RefinedRankTwoGain a c) :
    SharpGapStatement ∧ SharpEventualGapStatement := by
  apply sharpGapStatements_of_rank_gain
  intro a c hmono hpos ha hcl hcu hgap
  exact gapRankGain_of_structure_and_refined_rank_two hmono hpos ha hcl hcu hgap
    (powerSubsetStructure_of_dyadic hstructure) (h₂ a c hmono hpos ha hcl hcu hgap)

end Jsp000726
