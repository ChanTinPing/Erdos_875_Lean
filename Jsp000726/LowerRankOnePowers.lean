module

public import Jsp000726.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726

/-- Convert a power bound for the length of the protected prefix into a power bound
for the length of the progression. -/
theorem progression_length_le_rpow_of_prefix_bound {g m L B v C D : ℝ}
    (hg : 0 < g) (hL : 0 ≤ L) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (hm : D * (g * L) ^ (1 / B) ≤ m) (hupper : m ≤ C * g ^ v) :
    L ≤ (C / D) ^ B * g ^ (B * v - 1) := by
  have h : (g * L) ^ (B⁻¹) ≤ (C / D) * g ^ v := by
    rw [← mul_div_right_comm, le_div_iff₀ hD, mul_comm _ D]
    simpa only [one_div] using hm.trans hupper
  have h' := Real.rpow_le_rpow (Real.rpow_nonneg (mul_nonneg hg.le hL) _) h hB.le
  have hCnon : 0 ≤ C / D := div_nonneg hC.le hD.le
  rw [← Real.rpow_mul (mul_nonneg hg.le hL), inv_mul_cancel₀ hB.ne',
      Real.rpow_one, Real.mul_rpow hCnon (Real.rpow_nonneg hg.le _),
      ← Real.rpow_mul hg.le, mul_comm v B] at h'
  rw [Real.rpow_sub hg, Real.rpow_one, ← mul_div_assoc, le_div_iff₀ hg, mul_comm L g]
  exact h'

/-- In the uncapped case, residue packing gives the progression-length exponent
`B - 1 - B * v`, with a single constant independent of the progression. -/
theorem progression_length_le_rpow_of_uncapped_packing {g m L B v C D : ℝ}
    (hg : 0 < g) (hL : 0 ≤ L) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (hm : D * (g * L) ^ (1 / B) ≤ m) (hpack : C * m * g ^ v ≤ g) :
    L ≤ (C⁻¹ / D) ^ B * g ^ (B - 1 - B * v) := by
  have hsimple : m ≤ C⁻¹ * g ^ (1 - v) := by
    rw [Real.rpow_sub hg, Real.rpow_one, ← div_eq_inv_mul, div_div,
      le_div_iff₀ (mul_pos (Real.rpow_pos_of_pos hg _) hC)]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hpack
  exact (progression_length_le_rpow_of_prefix_bound hg hL hB (inv_pos.mpr hC) hD hm hsimple).trans_eq
    (by rw [show B * (1 - v) - 1 = B - 1 - B * v by ring])

/-- In the capped case, residue packing gives exponent `B / U - 1` for the
progression length when the protected prefix contributes a power `U`. -/
theorem progression_length_le_rpow_of_capped_packing {g m L B U C D : ℝ}
    (hg : 0 < g) (hL : 0 ≤ L) (hB : 0 < B) (hU : 0 < U) (hC : 0 < C) (hD : 0 < D)
    (hm : D * (g * L) ^ (1 / B) ≤ m) (hpack : C * m ^ U ≤ g) :
    L ≤ ((C⁻¹) ^ (1 / U) / D) ^ B * g ^ (B / U - 1) := by
  have hm0 : 0 ≤ m := (mul_nonneg hD.le (Real.rpow_nonneg (mul_nonneg hg.le hL) _)).trans hm
  have hpow : m ^ U ≤ C⁻¹ * g := by
    rwa [← div_eq_inv_mul, le_div_iff₀ hC, mul_comm]
  have hsimple : m ≤ C⁻¹ ^ (1 / U) * g ^ (1 / U) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hm0 U) hpow (one_div_nonneg.mpr hU.le)
    rwa [← Real.rpow_mul hm0, mul_one_div_cancel hU.ne', Real.rpow_one,
      Real.mul_rpow (inv_nonneg.mpr hC.le) hg.le] at h
  have h := progression_length_le_rpow_of_prefix_bound hg hL hB
    (Real.rpow_pos_of_pos (inv_pos.mpr hC) _) hD hm hsimple
  rwa [mul_one_div] at h

/-- Rank-one gain (4.2) from the finite progression and layer estimates.
The displayed coefficient is positive and uniform in `N`, `g`, and `L`. -/
theorem rankOne_layer_power_lower_bound {N g L F W v μ C D E : ℝ}
    (hN : 0 < N) (hg : 0 < g) (hv : 0 ≤ v) (hμ : 0 < μ)
    (hC : 0 < C) (hD : 0 < D) (hE : 0 < E)
    (hlen : D * N ^ (2 : ℝ) ≤ L) (hpacking : L ≤ C * g ^ μ)
    (hearly : E * g ^ v ≤ F) (hcount : F * L ≤ W) :
    E * (D / C) ^ (v / μ) * D * N ^ (2 + 2 * v / μ) ≤ W := by
  have hpower : D / C * N ^ (2 : ℝ) ≤ g ^ μ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hC]
    exact hlen.trans hpacking |>.trans_eq (mul_comm _ _)
  have h := Real.rpow_le_rpow
    (mul_nonneg (div_nonneg hD.le hC.le) (Real.rpow_nonneg hN.le _)) hpower
    (div_nonneg hv hμ.le)
  rw [Real.mul_rpow (div_nonneg hD.le hC.le) (Real.rpow_nonneg hN.le _),
    ← Real.rpow_mul hN.le, ← Real.rpow_mul hg.le, mul_comm μ, div_mul_cancel₀ _ hμ.ne'] at h
  have hF := (mul_le_mul_of_nonneg_left h hE.le).trans hearly
  have hlo : 0 ≤ E * ((D / C) ^ (v / μ) * N ^ (2 * (v / μ))) := by positivity
  have hL : 0 ≤ L := (mul_nonneg hD.le (Real.rpow_nonneg hN.le _)).trans hlen
  have hfinal := (mul_le_mul hF hlen (by positivity :
    0 ≤ D * N ^ (2 : ℝ)) ((hlo.trans hF).trans_eq rfl)).trans hcount
  rw [Real.rpow_add hN, show 2 * v / μ = 2 * (v / μ) by ring]
  exact (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hfinal)

/-- Both the capped and uncapped residue-packing alternatives imply (4.1).
The restriction on `v` makes the capped length exponent no larger. -/
theorem progression_length_le_rpow_of_packing_cases
    {g m L B c u v A C D : ℝ} (hg : 1 ≤ g) (hL : 0 ≤ L) (hB : 0 < B)
    (hu : 0 ≤ u) (huc : u + 1 ≤ c) (hv : v ≤ u / c) (hA : 0 < A)
    (hC : 0 < C) (hD : 0 < D) (hm : A * (g * L) ^ (1 / B) ≤ m)
    (hpack : C * m * g ^ v ≤ g ∨ D * m ^ (u + 1) ≤ g) :
    L ≤ max ((C⁻¹ / A) ^ B) (((D⁻¹) ^ (1 / (u + 1)) / A) ^ B) *
      g ^ (B - 1 - B * v) := by
  have hg' : 0 < g := zero_lt_one.trans_le hg
  have hu' : 0 < u + 1 := by positivity
  rcases hpack with hpack | hpack
  · exact (progression_length_le_rpow_of_uncapped_packing hg' hL hB hC hA hm hpack).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hg'.le _))
  · have hvu := hv.trans (div_le_div_of_nonneg_left hu hu' huc)
    rw [show u / (u + 1) = 1 - 1 / (u + 1) by field_simp; ring] at hvu
    have he : B / (u + 1) - 1 ≤ B - 1 - B * v := by
      nlinarith only [mul_le_mul_of_nonneg_left hvu hB.le, mul_one_div B (u + 1)]
    have hr := Real.rpow_le_rpow_of_exponent_le hg he
    have hcoef : 0 ≤ ((D⁻¹) ^ (1 / (u + 1)) / A) ^ B := by positivity
    exact (progression_length_le_rpow_of_capped_packing hg' hL hB hu' hD hA hm hpack).trans
      (mul_le_mul (le_max_right _ _) hr (Real.rpow_nonneg hg'.le _) (hcoef.trans (le_max_right _ _)))

/-- For the rank-one progression, a quadratic length bound and a step at most
`A * N^p` force the protected prefix to have size at least a constant times
`g^(1/p)`. Here `p` is the exponent of the step, one less than the term exponent. -/
theorem rankOne_protected_prefix_lower {N g L m p A D E : ℝ}
    (hN : 0 < N) (hg : 0 < g) (hp : 0 < p) (hA : 0 < A) (hD : 0 < D) (hE : 0 < E)
    (hstep : g ≤ A * N ^ p) (hlen : D * N ^ (2 : ℝ) ≤ L)
    (hm : E * (g * L) ^ (1 / (p + 2)) ≤ m) :
    E * (D / A ^ (2 / p)) ^ (1 / (p + 2)) * g ^ (1 / p) ≤ m := by
  have ha : 0 < A ^ (2 / p) := Real.rpow_pos_of_pos hA _
  have hh := Real.rpow_le_rpow hg.le hstep (by positivity : 0 ≤ (2 : ℝ) / p)
  have hfactor : p * (2 / p) = (2 : ℝ) := by field_simp
  rw [Real.mul_rpow hA.le (Real.rpow_nonneg hN.le _), ← Real.rpow_mul hN.le, hfactor] at hh
  have hl : D / A ^ (2 / p) * g ^ (2 / p) ≤ L := by
    calc
      D / A ^ (2 / p) * g ^ (2 / p) ≤
          D / A ^ (2 / p) * (A ^ (2 / p) * N ^ (2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hh (div_nonneg hD.le ha.le)
      _ = D * N ^ (2 : ℝ) := by field_simp
      _ ≤ L := hlen
  have hh' : D / A ^ (2 / p) * g ^ (1 + 2 / p) ≤ g * L := by
    rw [Real.rpow_add hg, Real.rpow_one]
    exact (by simpa only [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hl hg.le)
  have hD' : 0 < D / A ^ (2 / p) := div_pos hD ha
  have hpow := Real.rpow_le_rpow
    (mul_nonneg hD'.le (Real.rpow_nonneg hg.le _)) hh' (by positivity : 0 ≤ (1 : ℝ) / (p + 2))
  rw [Real.mul_rpow hD'.le (Real.rpow_nonneg hg.le _), ← Real.rpow_mul hg.le,
    show (1 + 2 / p) * (1 / (p + 2)) = 1 / p by field_simp] at hpow
  exact ((by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpow hE.le) :
    E * (D / A ^ (2 / p)) ^ (1 / (p + 2)) * g ^ (1 / p) ≤ _).trans hm

/-- The middle-layer bound at the capped prefix still supplies an early layer of
size at least a constant times `g^v` once the prefix is at least a power of `g`. -/
theorem rankOne_capped_layer_lower {g m F p u v E K : ℝ} (hg : 1 ≤ g)
    (hu : 0 ≤ u) (hv : v ≤ u / p) (hE : 0 < E) (hK : 0 < K)
    (hm : E * g ^ (1 / p) ≤ m) (hF : K * (m / 4) ^ u ≤ F) :
    K * (E / 4) ^ u * g ^ v ≤ F := by
  have hg0 : 0 ≤ g := zero_le_one.trans hg
  have hm' : E / 4 * g ^ (1 / p) ≤ m / 4 := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hm (by norm_num)
  have hh := Real.rpow_le_rpow
    (mul_nonneg (by positivity : 0 ≤ E / 4) (Real.rpow_nonneg hg0 _)) hm' hu
  rw [Real.mul_rpow (by positivity : 0 ≤ E / 4) (Real.rpow_nonneg hg0 _),
    ← Real.rpow_mul hg0, one_div_mul_eq_div] at hh
  have hv' := Real.rpow_le_rpow_of_exponent_le hg hv
  have hlo := mul_le_mul_of_nonneg_left hv' (Real.rpow_nonneg (by positivity : 0 ≤ E / 4) u)
  rw [mul_assoc]
  exact (mul_le_mul_of_nonneg_left (hlo.trans hh) hK.le).trans hF

end Jsp000726
