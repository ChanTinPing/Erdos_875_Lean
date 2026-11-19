module

public import Jsp000726.LowerEarlyBounds
public import Jsp000726.LowerContradiction

@[expose] public section

namespace Jsp000726

open Filter Finset

/-- A total subset-sum count lower bound yields a lower bound on the prefix weight. -/
theorem eventual_prefixWeight_of_allCounts {a : ℕ → ℕ} (hpos : ∀ n, 0 < a n) {u : ℝ}
    (h : PrefixPower (allCounts a) u) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop, A * ((n : ℝ) + 1) ^ u ≤ (prefixWeight a n : ℝ) := by
  obtain ⟨A, hA, h⟩ := h
  refine ⟨A / 2, by positivity, eventually_atTop.mpr ⟨1, fun n hn => ?_⟩⟩
  have hsum : (allCounts a n : ℝ) ≤ (prefixWeight a n : ℝ) + 1 := by
    exact_mod_cast allCounts_le_prefixWeight_add_one a n
  have hpos' : 1 ≤ (prefixWeight a n : ℝ) := by
    exact_mod_cast hn.trans (le_prefixWeight hpos n)
  have hh := h n
  linarith

/-- A middle-layer exponent above `c - 1` suffices to rule out the gap exponent `c`. -/
theorem not_eventual_gap_cap_of_middleLayer {a : ℕ → ℕ} (hmono : StrictMono a)
    (hpos : ∀ n, 0 < a n) (ha : Admissible a) {u c : ℝ} (hu : 0 ≤ u)
    (hcu : c < u + 1) (hW : PrefixPower (middleLayer a) u) :
    ¬ (∀ᶠ n : ℕ in atTop, (gap a n : ℝ) ≤ ((n : ℝ) + 1) ^ c) := by
  have hZ := prefixPower_allCounts_of_middleLayer ha hu hW
  obtain ⟨A, hA, h⟩ := eventual_prefixWeight_of_allCounts hpos hZ
  have hu' : 0 ≤ u + 1 := by linarith
  have hshort := eventual_shortened_prefix_growth hu' hA h
  have hconst := div_pos hA (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (u + 1))
  exact not_eventual_gap_cap_of_prefix_growth hmono hpos ha hcu hconst hshort

/-- The elementary cubic lower bound on feasible eventual gap exponents. -/
theorem three_le_of_eventualGapExponent {c : ℝ} (h : EventualGapExponent c) : 3 ≤ c := by
  by_contra! hc
  obtain ⟨a, hmono, hpos, ha, hgap⟩ := h
  exact not_eventual_gap_cap_of_middleLayer hmono hpos ha (by norm_num)
    (by linarith : c < (2 : ℝ) + 1) (prefixPower_middleLayer_two hmono) hgap

end Jsp000726
