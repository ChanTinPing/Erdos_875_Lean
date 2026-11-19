module

public import Jsp000726.LowerAsymptoticsRanks
public import Jsp000726.LowerGainChoice
public import Jsp000726.LowerRankTwoPowers

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

@[expose] public section

namespace Jsp000726

open Filter PublicStructure

/-- The two finite counts after choosing a protected prefix. The first packs its
different cardinalities into the original progression's span. The second packs
the new single layer into the middle layer of the full prefix. -/
def RankTwoCountBounds (a : ℕ → ℕ) (n : ℕ) (P : IntegerGAP) (c v A K E : ℝ) : Prop :=
  let M : ℝ := P.carrier.card
  let σ := rankTwoSigma c v
  ∃ R m : ℝ, 0 < R ∧
    A * (R * M) ^ (1 / (c + 2)) ≤ m ∧
    K * m * M * R ^ σ ≤ R * M ∧
    E * M * R ^ σ ≤ (middleLayer a n : ℝ)

/-- Uniform finite count bounds in rank two give the exact asymptotic exponent in
the manuscript. All losses are retained as explicit positive constants. -/
theorem oppositeRankGain_two_of_count_bounds {a : ℕ → ℕ} {c v w A K E : ℝ} {C : ℕ}
    (hcl : 4.55 ≤ c) (hcu : c ≤ 4.562) (hv₀ : 0 < v) (hv : v ≤ (c - 1) / c)
    (hw : w ≤ gapRankTwoGain c v) (hC : 0 < C) (hA : 0 < A) (hK : 0 < K) (hE : 0 < E)
    (hcount : ∀ᶠ n : ℕ in atTop, ∀ P : IntegerGAP, P.rank = 2 →
      OppositeLayerWitness a n C P → RankTwoCountBounds a n P c v A K E) :
    OppositeRankGain a C 2 w := by
  let σ := rankTwoSigma c v
  let B := c + 2
  let α := gapMu c σ
  let D : ℝ := ((32 : ℝ) ^ (3 : ℕ) * (C : ℝ))⁻¹
  let F : ℝ := (K⁻¹ / A) ^ B
  have hσ := rankTwoSigma_pos_lt hcl hcu hv₀ hv
  have hα : 0 < α := gapMu_pos_of_le hcl (hσ.2.le.trans hv)
  have hB : 0 < B := by dsimp [B]; linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hF : 0 < F := Real.rpow_pos_of_pos (div_pos (inv_pos.mpr hK) hA) _
  let Q : ℝ := E * D * (D / F) ^ (σ / α)
  have hQ : 0 < Q := mul_pos (mul_pos hE hD) (Real.rpow_pos_of_pos (div_pos hD hF) _)
  refine ⟨Q, hQ, ?_⟩
  filter_upwards [hcount, eventually_ge_atTop (16 : ℕ)] with n hn h16
  intro P hP hW
  let N : ℝ := (n : ℝ) + 1
  let M : ℝ := P.carrier.card
  obtain ⟨R, m, hR, hm, hpack, hlayer⟩ := hn P hP hW
  have hNc : (n + 1 : ℕ) ≤ 32 * (n / 16) := by omega
  have hcard : (n / 16) ^ (3 : ℕ) ≤ C * P.carrier.card := by
    simpa only [hP, Nat.reduceAdd] using hW.2.2.1
  have hNpow : (n + 1 : ℕ) ^ (3 : ℕ) ≤ 32 ^ (3 : ℕ) * C * P.carrier.card := by
    calc
      _ ≤ (32 * (n / 16)) ^ (3 : ℕ) := Nat.pow_le_pow_left hNc _
      _ = 32 ^ (3 : ℕ) * ((n / 16) ^ (3 : ℕ)) := mul_pow _ _ _
      _ ≤ _ := by rw [mul_assoc]; exact Nat.mul_le_mul_left _ hcard
  have hN : 0 < N := by dsimp [N]; positivity
  have hN₁ : 1 ≤ N := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hlarge : D * N ^ (3 : ℝ) ≤ M := by
    dsimp [D, N, M]
    rw [Real.rpow_ofNat, inv_mul_eq_div]
    apply (div_le_iff₀ (by positivity : 0 < (32 : ℝ) ^ (3 : ℕ) * (C : ℝ))).2
    rw [mul_comm ((P.carrier.card : ℕ) : ℝ)]
    exact_mod_cast hNpow
  have hM : 0 < M := (mul_pos hD (Real.rpow_pos_of_pos hN _)).trans_le hlarge
  have hvolume : M ≤ F * R ^ α := by
    have heq : B - 1 - B * σ = α := by dsimp [B, α, gapMu]; ring
    have h := rankTwo_volume_le_rpow_of_packing (σ := σ) hR hM hB hK hA hm hpack
    rw [heq] at h
    exact h
  have hgood := rankTwo_layer_power_lower_bound hN hR hα hσ.1.le hF hD hE hlarge hvolume hlayer
  have hbound : N ^ w ≤ N ^ (3 + 3 * σ / α) :=
    Real.rpow_le_rpow_of_exponent_le hN₁ hw
  exact (mul_le_mul_of_nonneg_left hbound hQ.le).trans hgood

end Jsp000726
