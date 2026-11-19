module

public import Jsp000726.Basic
public import Mathlib.Algebra.Order.Field.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726

private theorem quadratic_pos_of_discriminant_neg
    {A B C : ℝ} (hA : 0 < A) (hΔ : B ^ 2 < 4 * A * C) (x : ℝ) :
    0 < A * x ^ 2 + B * x + C := by
  have hsq : 0 ≤ (2 * A * x + B) ^ 2 := sq_nonneg _
  have hfactor : 4 * A * (A * x ^ 2 + B * x + C) =
      (2 * A * x + B) ^ 2 + (4 * A * C - B ^ 2) := by ring
  have hpos : 0 < 4 * A * (A * x ^ 2 + B * x + C) := by
    rw [hfactor]
    linarith
  exact pos_of_mul_pos_right hpos (by positivity)

/-- The rank-one exponent improves on the current exponent when the discriminant in
Section 5 is negative. -/
theorem rankOne_gain {c p u : ℝ} (hc : 0 < c) (hp : 0 < p)
    (hdisc : p * (c - 2) ^ 2 < 8 * c)
    (hden : 0 < p - (p + 1) * (u / c)) :
    u < 2 + 2 * (u / c) / (p - (p + 1) * (u / c)) := by
  have hd : (c * p + 2 * (p + 1) - 2) ^ 2 - 4 * (p + 1) * (2 * c * p) =
      p * (p * (c - 2) ^ 2 - 8 * c) := by ring
  have hdneg : p * (p * (c - 2) ^ 2 - 8 * c) < 0 :=
    mul_neg_of_pos_of_neg hp (sub_neg.mpr hdisc)
  have hq := quadratic_pos_of_discriminant_neg (A := p + 1)
    (B := -(c * p + 2 * (p + 1) - 2)) (C := 2 * c * p)
    (by linarith) (by nlinarith only [hd, hdneg]) u
  have hmul : c * (2 * (u / c) - (u - 2) * (p - (p + 1) * (u / c))) =
      (p + 1) * u ^ 2 + -(c * p + 2 * (p + 1) - 2) * u + 2 * c * p := by
    field_simp [ne_of_gt hc]
    ring
  have hgain : (u - 2) * (p - (p + 1) * (u / c)) < 2 * (u / c) := by
    have := pos_of_mul_pos_right (hmul ▸ hq) hc.le
    linarith
  exact sub_lt_iff_lt_add'.mp ((lt_div_iff₀ hden).2 hgain)

/-- The narrow interval below the sharp gap endpoint only needs the first numerical
certificate in the paper's rank-two argument. -/
theorem rankTwo_polynomial_pos_near_gap_threshold {c s : ℝ}
    (hcl : 4.55 ≤ c) (hcu : c ≤ 4.562) (hs : 0 ≤ s) (hsu : s ≤ c - 4) :
    0 < (28 / 25 : ℝ) * (s + 3) ^ 2 * (3 + (c + 2) * s) -
      c * (c + 1) ^ 2 * (c - 3 - s) * s := by
  let h : ℝ := 4.562
  let B : ℝ := 6.55
  let K : ℝ := h * (h + 1) ^ 2
  have hh : c ≤ h := hcu
  have hB : B ≤ c + 2 := by dsimp [B]; linarith
  have hcs : 0 ≤ c - 3 - s := by linarith
  have hc : 0 ≤ c := by linarith
  have hK : c * (c + 1) ^ 2 ≤ K := by
    apply mul_le_mul hh _ (sq_nonneg _) (hc.trans hh)
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hKnonneg : 0 ≤ K := by dsimp [K, h]; norm_num
  have hupper : c * (c + 1) ^ 2 * (c - 3 - s) * s ≤ K * (h - 3 - s) * s := by
    apply mul_le_mul_of_nonneg_right _ hs
    exact mul_le_mul hK (by linarith) hcs hKnonneg
  have hlower : (28 / 25 : ℝ) * (s + 3) ^ 2 * (3 + B * s) ≤
      (28 / 25 : ℝ) * (s + 3) ^ 2 * (3 + (c + 2) * s) := by
    apply mul_le_mul_of_nonneg_left
    · exact add_le_add_right (mul_le_mul_of_nonneg_right hB hs) _
    · positivity
  let A₂ : ℝ := (28 / 25 : ℝ) * (3 + 6 * B) + K
  let B₂ : ℝ := (28 / 25 : ℝ) * (18 + 9 * B) - K * (h - 3)
  let C₂ : ℝ := (28 / 25 : ℝ) * 27
  have hA₂ : 0 < A₂ := by dsimp [A₂, B, K, h]; norm_num
  have hΔ : B₂ ^ 2 < 4 * A₂ * C₂ := by dsimp [A₂, B₂, C₂, B, K, h]; norm_num
  have hq := quadratic_pos_of_discriminant_neg hA₂ hΔ s
  have hexpand : (28 / 25 : ℝ) * (s + 3) ^ 2 * (3 + B * s) -
      K * (h - 3 - s) * s =
      (A₂ * s ^ 2 + B₂ * s + C₂) + (28 / 25 : ℝ) * B * s ^ 3 := by
    dsimp [A₂, B₂, C₂]
    ring
  have hcubic : 0 ≤ (28 / 25 : ℝ) * B * s ^ 3 := by dsimp [B]; positivity
  calc
    0 < (A₂ * s ^ 2 + B₂ * s + C₂) + (28 / 25 : ℝ) * B * s ^ 3 := add_pos_of_pos_of_nonneg hq hcubic
    _ = (28 / 25 : ℝ) * (s + 3) ^ 2 * (3 + B * s) - K * (h - 3 - s) * s := hexpand.symm
    _ ≤ _ := sub_le_sub hlower hupper

/-- The gap endpoint lies in the first numerical interval in Section 5. -/
theorem gapThreshold_lt_4562 : gapThreshold < 4.562 := by
  have hsq : (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have hs : Real.sqrt 17 < 4.124 := by
    by_contra! h
    have hbound := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4.124) h 2
    linarith only [hsq, hbound]
  unfold gapThreshold
  linarith

private theorem gap_mu_pos {c u : ℝ} (hc : 4.55 ≤ c) (hu : u ≤ c - 1) :
    0 < (c + 1) - (c + 2) * (u / c) := by
  have hcpos : 0 < c := by linarith
  have hfactor : c * ((c + 1) - (c + 2) * (u / c)) =
      2 + (c + 2) * ((c - 1) - u) := by
    field_simp [ne_of_gt hcpos]
    ring
  have hpos : 0 < 2 + (c + 2) * ((c - 1) - u) :=
    add_pos_of_pos_of_nonneg (by norm_num)
      (mul_nonneg (by linarith) (sub_nonneg.mpr hu))
  exact pos_of_mul_pos_right (hfactor.symm ▸ hpos) hcpos.le

/-- Rank one gives a strict increase at every bootstrap exponent below the gap threshold. -/
theorem rankOne_gain_for_gap {c u : ℝ} (hc : 4.55 ≤ c) (hc₀ : c < gapThreshold)
    (hu : u ≤ c - 1) :
    u < 2 + 2 * (u / c) / ((c + 1) - (c + 2) * (u / c)) := by
  have hs : 0 ≤ Real.sqrt 17 := Real.sqrt_nonneg _
  have hsq : (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have hroot1 : 0 < c - (5 - Real.sqrt 17) / 2 := by linarith
  have hroot2 : c - (5 + Real.sqrt 17) / 2 < 0 := sub_neg.mpr hc₀
  have hpoly : c ^ 2 - 5 * c + 2 < 0 := by
    have hprod := mul_neg_of_pos_of_neg hroot1 hroot2
    nlinarith only [hprod, hsq]
  have hdiscEq : (c + 1) * (c - 2) ^ 2 - 8 * c =
      (c + 2) * (c ^ 2 - 5 * c + 2) := by ring
  have hdisc := (sub_neg.mp (hdiscEq.symm ▸ mul_neg_of_pos_of_neg (by linarith) hpoly))
  have hadd : c + 1 + 1 = c + 2 := by ring
  have hden : 0 < (c + 1) - (c + 1 + 1) * (u / c) := by
    rw [hadd]
    exact gap_mu_pos hc hu
  simpa only [hadd] using rankOne_gain (by linarith) (by linarith) hdisc hden

/-- Auxiliary exponent from the rank-two chain separation. -/
noncomputable def rankTwoSigma (c v : ℝ) : ℝ :=
  (28 / 25 : ℝ) * v ^ 2 / ((c + 1) * (1 - v))

/-- For the gap endpoint calculation, the rank-two exponent also strictly increases
on the range where the direct cubic bound does not suffice. -/
theorem rankTwo_gain_for_gap {c u : ℝ} (hcl : 4.55 ≤ c) (hcu : c ≤ 4.562)
    (hul : 3 ≤ u) (huu : u ≤ c - 1) :
    let σ := rankTwoSigma c (u / c)
    u < 3 + 3 * σ / ((c + 1) - (c + 2) * σ) := by
  let v := u / c
  let σ := rankTwoSigma c v
  change u < 3 + 3 * σ / ((c + 1) - (c + 2) * σ)
  have hc : 0 < c := by linarith
  have hv0 : 0 < v := div_pos (by linarith) hc
  have huv : v ≤ (c - 1) / c := div_le_div_of_nonneg_right huu hc.le
  have hv1 : v < 1 := by
    exact (div_lt_one (by linarith : 0 < c)).mpr (by linarith)
  have hprod : 0 < (c + 1) * (1 - v) := mul_pos (by linarith) (by linarith)
  have hslack : (28 / 25 : ℝ) * v < (c + 1) * (1 - v) := by
    have hmul := mul_le_mul_of_nonneg_left huv (by linarith : 0 ≤ c + 1 + 28 / 25)
    have hb : (c + 1 + 28 / 25) * ((c - 1) / c) < c + 1 := by
      rw [← mul_div_assoc, div_lt_iff₀ hc]
      nlinarith only [hcl, hcu]
    have := hmul.trans_lt hb
    linarith only [this]
  have hσv : σ < v := by
    have h := mul_lt_mul_of_pos_left hslack hv0
    apply (div_lt_iff₀ hprod).2
    change (28 / 25 : ℝ) * v ^ 2 < v * ((c + 1) * (1 - v))
    nlinarith only [h]
  have hden : 0 < (c + 1) - (c + 2) * σ :=
    (gap_mu_pos hcl huu).trans
      (sub_lt_sub_left (mul_lt_mul_of_pos_left hσv (by linarith)) _)
  have hpoly := rankTwo_polynomial_pos_near_gap_threshold hcl hcu
    (show 0 ≤ u - 3 by linarith) (show u - 3 ≤ c - 4 by linarith)
  have heq : c ^ 2 * ((28 / 25 : ℝ) * v ^ 2 * (3 + (c + 2) * (u - 3)) -
      ((c + 1) * (1 - v)) * ((c + 1) * (u - 3))) =
      (28 / 25 : ℝ) * (u - 3 + 3) ^ 2 * (3 + (c + 2) * (u - 3)) -
        c * (c + 1) ^ 2 * (c - 3 - (u - 3)) * (u - 3) := by
    dsimp [v]
    field_simp [ne_of_gt hc]
    ring
  have hcalc := pos_of_mul_pos_right (heq.symm ▸ hpoly) (sq_nonneg c)
  have hratio : (c + 1) * (u - 3) < σ * (3 + (c + 2) * (u - 3)) := by
    dsimp [σ, rankTwoSigma]
    rw [div_mul_eq_mul_div, lt_div_iff₀ hprod]
    linarith only [hcalc]
  apply sub_lt_iff_lt_add'.mp
  apply (lt_div_iff₀ hden).mpr
  linarith only [hratio]

end Jsp000726
