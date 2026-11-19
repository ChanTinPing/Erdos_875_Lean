module

public import Jsp000726.LowerExponents
public import Jsp000726.LowerIteration

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726

noncomputable def gapMu (c v : ℝ) : ℝ :=
  c + 1 - (c + 2) * v

noncomputable def gapRankOneGain (c v : ℝ) : ℝ :=
  2 + 2 * v / gapMu c v

noncomputable def gapRankTwoGain (c v : ℝ) : ℝ :=
  3 + 3 * rankTwoSigma c v / gapMu c (rankTwoSigma c v)

theorem gapMu_pos_of_le {c v : ℝ} (hc : 4.55 ≤ c) (hv : v ≤ (c - 1) / c) :
    0 < gapMu c v := by
  have hc₀ : 0 < c := by linarith
  have hconst : c * gapMu c ((c - 1) / c) = 2 := by
    unfold gapMu
    field_simp [hc₀.ne']
    ring
  have hμ : 0 < gapMu c ((c - 1) / c) :=
    pos_of_mul_pos_right (hconst.symm ▸ (by norm_num : (0 : ℝ) < 2)) hc₀.le
  have hmono : gapMu c ((c - 1) / c) ≤ gapMu c v := by
    unfold gapMu
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left hv (by linarith)) _
  exact hμ.trans_le hmono

theorem rankTwoSigma_pos_lt {c v : ℝ} (hcl : 4.55 ≤ c) (hcu : c ≤ 4.562)
    (hv₀ : 0 < v) (hv : v ≤ (c - 1) / c) :
    0 < rankTwoSigma c v ∧ rankTwoSigma c v < v := by
  have hc : 0 < c := by linarith
  have hv₁ : v < 1 := hv.trans_lt ((div_lt_one hc).2 (by linarith))
  have hprod : 0 < (c + 1) * (1 - v) := mul_pos (by linarith) (by linarith)
  have hslack : (28 / 25 : ℝ) * v < (c + 1) * (1 - v) := by
    have hmul := mul_le_mul_of_nonneg_left hv (by linarith : 0 ≤ c + 1 + 28 / 25)
    have hb : (c + 1 + 28 / 25) * ((c - 1) / c) < c + 1 := by
      rw [← mul_div_assoc, div_lt_iff₀ hc]
      nlinarith only [hcl, hcu]
    linarith only [hmul.trans_lt hb]
  unfold rankTwoSigma
  refine ⟨div_pos (by positivity) hprod, (div_lt_iff₀ hprod).2 ?_⟩
  nlinarith only [mul_lt_mul_of_pos_left hslack hv₀]

private theorem gapRankOneGain_continuousAt {c v : ℝ} (hμ : 0 < gapMu c v) :
    ContinuousAt (gapRankOneGain c) v := by
  unfold gapRankOneGain gapMu at *
  fun_prop (disch := exact hμ.ne')

private theorem gapRankTwoGain_continuousAt {c v : ℝ}
    (hσ : 0 < (c + 1) * (1 - v)) (hμ : 0 < gapMu c (rankTwoSigma c v)) :
    ContinuousAt (gapRankTwoGain c) v := by
  unfold gapRankTwoGain gapMu rankTwoSigma at *
  fun_prop (disch := first | exact hσ.ne' | exact hμ.ne')

/-- Simultaneously choose the exponent below `u/c` required by the early-layer
estimate. Below three the direct cubic rank-two bound suffices. At and above
three the refined rank-two gain remains strict under this perturbation. -/
theorem gap_rank_gains_choose {c u : ℝ} (hc : 4.55 ≤ c) (hc₀ : c < gapThreshold)
    (hu₀ : 2 ≤ u) (hu₁ : u ≤ c - 1) :
    ∃ v : ℝ, 0 < v ∧ v < u / c ∧ 0 < gapMu c v ∧ u < gapRankOneGain c v ∧
      (u < 3 ∨ (3 / 5 < v ∧ u < gapRankTwoGain c v)) := by
  have hcp : 0 < c := by linarith
  have hcu : c ≤ 4.562 := hc₀.le.trans gapThreshold_lt_4562.le
  let z := u / c
  have hz : 0 < z := div_pos (by linarith) hcp
  have hzlast : z ≤ (c - 1) / c := div_le_div_of_nonneg_right hu₁ hcp.le
  have hμ := gapMu_pos_of_le hc hzlast
  have hF1 : u < gapRankOneGain c z := rankOne_gain_for_gap hc hc₀ hu₁
  have hcont₁ := gapRankOneGain_continuousAt hμ
  by_cases hu : u < 3
  · obtain ⟨v, hv, hFv⟩ := exists_left_of_continuousAt_lt hz hcont₁ hF1
    exact ⟨v, hv.1, hv.2, gapMu_pos_of_le hc (hv.2.le.trans hzlast), hFv, Or.inl hu⟩
  · have hu₃ := le_of_not_gt hu
    have hF2 : u < gapRankTwoGain c z := rankTwo_gain_for_gap hc hcu hu₃ hu₁
    have hσ := rankTwoSigma_pos_lt hc hcu hz hzlast
    have hμσ := gapMu_pos_of_le hc (hσ.2.le.trans hzlast)
    have hzlt : z < 1 := hzlast.trans_lt ((div_lt_one hcp).2 (by linarith))
    have hσden : 0 < (c + 1) * (1 - z) := mul_pos (by linarith) (by linarith)
    have hcont₂ := gapRankTwoGain_continuousAt hσden hμσ
    have hzlow : (3 / 5 : ℝ) < z := (lt_div_iff₀ hcp).2 (by linarith)
    obtain ⟨v, hv, hFv⟩ := exists_left_of_continuousAt_lt hzlow
      (hcont₁.min hcont₂) (lt_min hF1 hF2)
    exact ⟨v, lt_trans (by norm_num) hv.1, hv.2, gapMu_pos_of_le hc (hv.2.le.trans hzlast),
      hFv.trans_le (min_le_left _ _), Or.inr ⟨hv.1, hFv.trans_le (min_le_right _ _)⟩⟩

/-- Combine the rank-specific exponent bounds without assuming a fixed rank over all
large indices. Each proposed exponent must meet the bounds of every possible rank. -/
theorem exists_layer_exponent_of_rank_bounds {P : ℝ → Prop} {c : ℝ}
    (hc : 4.55 ≤ c) (hc₀ : c < gapThreshold) (base : P 2)
    (advance : ∀ u ∈ Set.Icc (2 : ℝ) (c - 1), P u →
      ∀ v : ℝ, 0 < v → v < u / c → 0 < gapMu c v →
      ∀ w : ℝ, w ≤ gapRankOneGain c v → w ≤ 4 →
      (w ≤ 3 ∨ (2.99 ≤ u ∧ 3 / 5 < v ∧ w ≤ gapRankTwoGain c v)) →
      P w) :
    ∃ w > c - 1, P w := by
  have hcp : 0 < c := by linarith
  have hc_hi : c < 4.562 := hc₀.trans gapThreshold_lt_4562
  refine exists_exponent_gt_of_local_step base ?_
  intro t ht
  have ht4 : t < 4 := by linarith [ht.2]
  obtain ⟨v, hv₀, hv, hμ, hF₁, hR₂⟩ := gap_rank_gains_choose hc hc₀ ht.1 ht.2
  have hcv : c * v < t := by simpa only [mul_comm] using (lt_div_iff₀ hcp).1 hv
  by_cases htlt : t < 3
  · let w := min 4 (min (gapRankOneGain c v) 3)
    have htw : t < w := lt_min ht4 (lt_min hF₁ htlt)
    refine ⟨c * v, hcv, fun u hu hlu hPu => ⟨w, htw, ?_⟩⟩
    exact advance u ⟨hu.1, hu.2.trans ht.2⟩ hPu v hv₀
      ((lt_div_iff₀ hcp).2 (by simpa only [mul_comm] using hlu)) hμ w
      ((min_le_right _ _).trans (min_le_left _ _)) (min_le_left _ _)
      (Or.inl ((min_le_right _ _).trans (min_le_right _ _)))
  · obtain ⟨hvlow, hF₂⟩ := hR₂.resolve_left htlt
    let w := min 4 (min (gapRankOneGain c v) (gapRankTwoGain c v))
    have htw : t < w := lt_min ht4 (lt_min hF₁ hF₂)
    have htl : (2.99 : ℝ) < t := by linarith [le_of_not_gt htlt]
    refine ⟨max (c * v) 2.99, max_lt hcv htl, fun u hu hlu hPu => ⟨w, htw, ?_⟩⟩
    have hvu := (le_max_left (c * v) (2.99 : ℝ)).trans_lt hlu
    have hu₂ := (le_max_right (c * v) (2.99 : ℝ)).trans hlu.le
    exact advance u ⟨hu.1, hu.2.trans ht.2⟩ hPu v hv₀
      ((lt_div_iff₀ hcp).2 (by simpa only [mul_comm] using hvu)) hμ w
      ((min_le_right _ _).trans (min_le_left _ _)) (min_le_left _ _)
      (Or.inr ⟨hu₂, hvlow, (min_le_right _ _).trans (min_le_right _ _)⟩)

end Jsp000726
