module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726

/-- Remove a positive power and a constant from a power inequality. -/
theorem lower_power_of_le_mul_power {x y C α γ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hC : 0 < C) (hγ : 0 < γ) (h : x ^ α ≤ C * y ^ γ) :
    C⁻¹ ^ γ⁻¹ * x ^ (α / γ) ≤ y := by
  have h' : C⁻¹ * x ^ α ≤ y ^ γ := by
    have hm : C⁻¹ * x ^ α = x ^ α / C := by rw [div_eq_mul_inv, mul_comm]
    rw [hm]
    exact (div_le_iff₀ hC).2 (by simpa only [mul_comm] using h)
  have hr := Real.rpow_le_rpow (mul_nonneg (inv_nonneg.mpr hC.le) (Real.rpow_nonneg hx _)) h' (inv_nonneg.mpr hγ.le)
  rw [Real.mul_rpow (inv_nonneg.mpr hC.le) (Real.rpow_nonneg hx _),
    ← Real.rpow_mul hx, ← Real.rpow_mul hy, mul_inv_cancel₀ hγ.ne', Real.rpow_one,
    ← div_eq_mul_inv] at hr
  exact hr

/-- Apply two power bounds to eliminate an intermediate scale. -/
theorem lower_power_of_two_scales {x y p B C α u r : ℝ} (hx : 0 ≤ x) (hp : 0 < p)
    (hB : 0 < B) (hC : 0 < C) (hu : 0 < u) (hr : 0 ≤ r)
    (hscale : B * p ^ u ≤ y) (hmain : x ^ α ≤ C * y * p ^ r) :
    (C * (B⁻¹ ^ (r / u)))⁻¹ ^ (1 + r / u)⁻¹ * x ^ (α / (1 + r / u)) ≤ y := by
  have hy : 0 < y := (mul_pos hB (Real.rpow_pos_of_pos hp _)).trans_le hscale
  have hscale' : p ^ u ≤ B⁻¹ * y := by
    rw [mul_comm, ← div_eq_mul_inv]
    apply (le_div_iff₀ hB).2
    simpa only [mul_comm] using hscale
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hp.le _) hscale' (div_nonneg hr hu.le)
  rw [← Real.rpow_mul hp.le, Real.mul_rpow (inv_nonneg.mpr hB.le) hy.le] at hpow
  have heq : u * (r / u) = r := by field_simp
  rw [heq] at hpow
  have hm : x ^ α ≤ (C * B⁻¹ ^ (r / u)) * y ^ (1 + r / u) := by
    calc
      x ^ α ≤ C * y * p ^ r := hmain
      _ ≤ C * y * (B⁻¹ ^ (r / u) * y ^ (r / u)) :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg hC.le hy.le)
      _ = (C * B⁻¹ ^ (r / u)) * y ^ (1 + r / u) := by
        rw [Real.rpow_add hy 1, Real.rpow_one]
        ring
  exact lower_power_of_le_mul_power hx hy.le (mul_pos hC (Real.rpow_pos_of_pos (inv_pos.mpr hB) _))
    (by have hd := div_nonneg hr hu.le; linarith) hm

/-- Eliminate the largest term from the early-count moment estimate. -/
theorem prefix_moment_of_weight_and_gap {S A Z p C D c w : ℝ} (hS : 0 < S) (hA : 0 ≤ A)
    (hZ : 0 ≤ Z) (hp : 0 < p) (hC : 0 < C) (hD : 0 < D) (hw : w ≤ 1)
    (hweight : S ≤ C * Z * A ^ (1 - w)) (hgap : A ^ 2 ≤ D * S * p ^ c) :
    S ^ ((1 + w) / 2) ≤ (C * D ^ ((1 - w) / 2)) * Z * p ^ (c * ((1 - w) / 2)) := by
  let θ := (1 - w) / 2
  have hθ : 0 ≤ θ := by dsimp [θ]; linarith
  have ha := Real.rpow_le_rpow (sq_nonneg A) hgap hθ
  have hη : (2 : ℝ) * θ = 1 - w := by dsimp [θ]; ring
  have heq : (A ^ 2) ^ θ = A ^ (1 - w) := by
    rw [show A ^ (2 : ℕ) = A ^ (2 : ℝ) by norm_num, ← Real.rpow_mul hA, hη]
  rw [heq, Real.mul_rpow (mul_nonneg hD.le hS.le) (Real.rpow_nonneg hp.le _),
    Real.mul_rpow hD.le hS.le, ← Real.rpow_mul hp.le] at ha
  have hm := hweight.trans (mul_le_mul_of_nonneg_left ha (mul_nonneg hC.le hZ))
  have haα : (1 + w) / 2 + θ = 1 := by dsimp [θ]; ring
  have hsplit : S ^ ((1 + w) / 2) * S ^ θ = S := by
    rw [← Real.rpow_add hS, haα, Real.rpow_one]
  have hcancel : S ^ ((1 + w) / 2) * S ^ θ ≤
      ((C * D ^ θ) * Z * p ^ (c * θ)) * S ^ θ := by
    rw [hsplit]
    convert hm using 1
    ring
  exact (mul_le_mul_iff_of_pos_right (Real.rpow_pos_of_pos hS θ)).mp hcancel

end Jsp000726
