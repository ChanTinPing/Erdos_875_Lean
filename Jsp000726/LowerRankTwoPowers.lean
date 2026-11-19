module

public import Jsp000726.LowerRankOnePowers

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726

/-- The prefix translates occupy a span proportional to `R*M`. A lower bound on
their count gives the rank-two relation between the volume `M` and spacing `R`. -/
theorem rankTwo_volume_le_rpow_of_packing {R M m B σ C D : ℝ}
    (hR : 0 < R) (hM : 0 < M) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (hm : D * (R * M) ^ (1 / B) ≤ m)
    (hpack : C * m * M * R ^ σ ≤ R * M) :
    M ≤ (C⁻¹ / D) ^ B * R ^ (B - 1 - B * σ) := by
  have hpack' : C * m * R ^ σ ≤ R := by
    apply le_of_mul_le_mul_right _ hM
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hpack
  exact progression_length_le_rpow_of_uncapped_packing hR hM.le hB hC hD hm hpack'

/-- A rank-two volume bound translates the augmented layer count into the desired power of N. -/
theorem rankTwo_layer_power_lower_bound {N R M W α σ C D E : ℝ}
    (hN : 0 < N) (hR : 0 < R) (hα : 0 < α) (hσ : 0 ≤ σ)
    (hC : 0 < C) (hD : 0 < D) (hE : 0 < E)
    (hlarge : D * N ^ (3 : ℝ) ≤ M) (hvolume : M ≤ C * R ^ α)
    (hlayer : E * M * R ^ σ ≤ W) :
    E * D * (D / C) ^ (σ / α) * N ^ (3 + 3 * σ / α) ≤ W := by
  have hpow : D / C * N ^ (3 : ℝ) ≤ R ^ α := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hC, mul_comm (R ^ α)]
    exact hlarge.trans hvolume
  have hspace := Real.rpow_le_rpow
    (mul_nonneg (div_nonneg hD.le hC.le) (Real.rpow_nonneg hN.le _)) hpow
      (div_nonneg hσ hα.le)
  rw [Real.mul_rpow (div_nonneg hD.le hC.le) (Real.rpow_nonneg hN.le _),
    ← Real.rpow_mul hN.le, ← Real.rpow_mul hR.le, mul_comm α,
    div_mul_cancel₀ _ hα.ne'] at hspace
  have hprod : (D * N ^ (3 : ℝ)) * ((D / C) ^ (σ / α) * N ^ (3 * (σ / α))) ≤ M * R ^ σ :=
    mul_le_mul hlarge hspace (by positivity : 0 ≤ (D / C) ^ (σ / α) * N ^ (3 * (σ / α)))
      ((by positivity : 0 ≤ D * N ^ (3 : ℝ)).trans hlarge)
  have hfinal := (mul_le_mul_of_nonneg_left hprod hE.le).trans_eq (show E * (M * R ^ σ) =
      E * M * R ^ σ by ring) |>.trans hlayer
  rw [Real.rpow_add hN, show 3 * σ / α = 3 * (σ / α) by ring]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hfinal

/-- An early support controlled by the spacing to the power `1 + δ` occupies a
vanishing fraction of the protected prefix when the displayed exponent is negative. -/
theorem rankTwo_protected_prefix_ratio_le {N V M m t B U δ A C D E : ℝ}
    (hN : 0 < N) (hV : 0 < V) (hM : 0 < M) (ht : 0 ≤ t)
    (hB : 0 < B) (hU : 0 < U) (hβ : 1 / B ≤ (1 + δ) / U)
    (hA : 0 < A) (hC : 0 < C) (hD : 0 < D) (hE : 0 < E)
    (htail : t ^ U ≤ A * (V / M) ^ (1 + δ))
    (hprefix : E * V ^ (1 / B) ≤ m)
    (hspan : V ≤ C * N ^ B) (hvolume : D * N ^ (3 : ℝ) ≤ M) :
    let β := (1 + δ) / U
    let γ := β - 1 / B
    t / m ≤ (A ^ (1 / U) / E) * (C ^ γ / D ^ β) * N ^ ((B - 3) * β - 1) := by
  let β := (1 + δ) / U
  let γ := β - 1 / B
  change t / m ≤ (A ^ (1 / U) / E) * (C ^ γ / D ^ β) * N ^ ((B - 3) * β - 1)
  have hβ0 : 0 ≤ β := (one_div_nonneg.mpr hB.le).trans hβ
  have hγ0 : 0 ≤ γ := sub_nonneg.mpr hβ
  have hvmp : 0 < V / M := div_pos hV hM
  have hd0 : 0 < E * V ^ (1 / B) := mul_pos hE (Real.rpow_pos_of_pos hV _)
  have hm : 0 < m := hd0.trans_le hprefix
  have htp := Real.rpow_le_rpow (Real.rpow_nonneg ht _) htail (one_div_nonneg.mpr hU.le)
  rw [← Real.rpow_mul ht, mul_one_div_cancel hU.ne', Real.rpow_one,
    Real.mul_rpow hA.le (Real.rpow_nonneg hvmp.le _), ← Real.rpow_mul hvmp.le, mul_one_div] at htp
  have htr : t / m ≤ (A ^ (1 / U) / E) * (V ^ γ / M ^ β) := by
    calc
      _ ≤ (A ^ (1 / U) * (V / M) ^ β) / m := div_le_div_of_nonneg_right htp hm.le
      _ ≤ (A ^ (1 / U) * (V / M) ^ β) / (E * V ^ (1 / B)) :=
        div_le_div_of_nonneg_left (by positivity) hd0 hprefix
      _ = _ := by
        rw [Real.div_rpow hV.le hM.le]
        change (A ^ (1 / U) * (V ^ β / M ^ β)) / (E * V ^ (1 / B)) =
          (A ^ (1 / U) / E) * (V ^ (β - 1 / B) / M ^ β)
        rw [Real.rpow_sub hV]
        field_simp
  apply htr.trans
  have hnum := Real.rpow_le_rpow hV.le hspan hγ0
  rw [Real.mul_rpow hC.le (Real.rpow_nonneg hN.le _), ← Real.rpow_mul hN.le] at hnum
  have hden := Real.rpow_le_rpow (by positivity : 0 ≤ D * N ^ (3 : ℝ)) hvolume hβ0
  rw [Real.mul_rpow hD.le (Real.rpow_nonneg hN.le _), ← Real.rpow_mul hN.le] at hden
  have hfrac : V ^ γ / M ^ β ≤ (C ^ γ * N ^ (B * γ)) / (D ^ β * N ^ (3 * β)) := by
    calc
      _ ≤ (C ^ γ * N ^ (B * γ)) / M ^ β :=
        div_le_div_of_nonneg_right hnum (Real.rpow_nonneg hM.le _)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  have hexp : B * γ - 3 * β = (B - 3) * β - 1 := by
    dsimp only [γ]
    field_simp
    ring
  calc
    _ ≤ (A ^ (1 / U) / E) * ((C ^ γ * N ^ (B * γ)) / (D ^ β * N ^ (3 * β))) :=
      mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = _ := by
      rw [← hexp, Real.rpow_sub hN]
      field_simp

/-- The protected-prefix estimate is sublinear in the manuscript's rank-two range. -/
theorem rankTwo_support_exponents {c u : ℝ} (_hcl : 4.55 ≤ c) (hcu : c ≤ 4.562)
    (hul : 2.99 ≤ u) (huu : u ≤ c - 1) :
    1 / (c + 2) ≤ (1 + (3 / 25 : ℝ)) / (u + 1) ∧
    ((c + 2) - 3) * ((1 + (3 / 25 : ℝ)) / (u + 1)) - 1 < 0 := by
  have hu : 0 < u + 1 := by linarith
  constructor
  · calc
      1 / (c + 2) ≤ 1 / (u + 1) :=
        div_le_div_of_nonneg_left zero_le_one hu (by linarith)
      _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) hu.le
  · apply sub_neg.mpr
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hu).2
    linarith

end Jsp000726
