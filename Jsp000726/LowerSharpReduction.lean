module

public import Jsp000726.LowerCubic
public import Jsp000726.LowerGainChoice
public import Jsp000726.LowerGrowth
public import Jsp000726.UpperSharp

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

namespace Jsp000726

open Filter

/-- The combinatorial gain from the three possible ranks of a progression.
All the exponents and the conditions under which they apply are explicit. -/
def GapRankGain (a : ℕ → ℕ) (c : ℝ) : Prop :=
  ∀ u ∈ Set.Icc (2 : ℝ) (c - 1), PrefixPower (middleLayer a) u →
    ∀ v : ℝ, 0 < v → v < u / c → 0 < gapMu c v →
    ∀ w : ℝ, w ≤ gapRankOneGain c v → w ≤ 4 →
      (w ≤ 3 ∨ (2.99 ≤ u ∧ 3 / 5 < v ∧ w ≤ gapRankTwoGain c v)) →
      PrefixPower (middleLayer a) w

/-- The layer gain is precisely the combinatorial input needed for the sharp
obstruction. The other steps are checked, including the final large-gap contradiction. -/
theorem not_eventual_gap_cap_of_rank_gain {a : ℕ → ℕ} (hmono : StrictMono a)
    (hpos : ∀ i, 0 < a i) (ha : Admissible a) {c : ℝ}
    (hcl : 4.55 ≤ c) (hcu : c < gapThreshold) (hgain : GapRankGain a c) :
    ¬ (∀ᶠ n : ℕ in atTop, (gap a n : ℝ) ≤ (n + 1 : ℝ) ^ c) := by
  obtain ⟨w, hw, hW⟩ := exists_layer_exponent_of_rank_bounds hcl hcu
    (prefixPower_middleLayer_two hmono) hgain
  exact not_eventual_gap_cap_of_middleLayer hmono hpos ha (by linarith) (by linarith) hW

private theorem four_fifty_five_lt_gapThreshold : (4.55 : ℝ) < gapThreshold := by
  have hsq : (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have hpos : 0 ≤ Real.sqrt 17 := Real.sqrt_nonneg 17
  have hroot : (4.1 : ℝ) < Real.sqrt 17 := by
    by_contra! h
    have h' := pow_le_pow_left₀ hpos h 2
    linarith only [h', hsq]
  unfold gapThreshold
  linarith

/-- It suffices to prove the combinatorial gain for exponents immediately below the
endpoint. Monotonicity and the verified sharp construction cover all other exponents. -/
theorem sharpGapStatements_of_rank_gain
    (hgain : ∀ (a : ℕ → ℕ) (c : ℝ), StrictMono a → (∀ i, 0 < a i) →
      Admissible a → 4.55 ≤ c → c < gapThreshold →
      (∀ᶠ n : ℕ in atTop, (gap a n : ℝ) ≤ (n + 1 : ℝ) ^ c) → GapRankGain a c) :
    SharpGapStatement ∧ SharpEventualGapStatement := by
  apply sharpGapStatements_of_bounds Upper.gapExponent_gapThreshold
  intro c h
  by_contra! hc
  let d := max c (4.55 : ℝ)
  have hdl : 4.55 ≤ d := le_max_right _ _
  have hdu : d < gapThreshold := max_lt hc four_fifty_five_lt_gapThreshold
  obtain ⟨a, hmono, hpos, ha, hgap⟩ := EventualGapExponent.mono h (show c ≤ d from le_max_left _ _)
  exact not_eventual_gap_cap_of_rank_gain hmono hpos ha hdl hdu
    (hgain a d hmono hpos ha hdl hdu hgap) hgap

end Jsp000726
