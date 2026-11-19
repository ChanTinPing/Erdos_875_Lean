module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Order.Filter.AtTopBot.Archimedean

@[expose] public section

open Filter

namespace Jsp000726.PublicStructure

/-- A sub-sixth-power ambient interval is eventually bounded by the sixth power of any
cardinality that grows at least linearly. -/
theorem eventually_ambient_le_card_sixth {size ambient : ℕ → ℕ} {p B δ : ℝ}
    (hp : p < 6) (hδ : 0 < δ)
    (hambient : ∀ᶠ n : ℕ in atTop, (ambient n : ℝ) ≤ B * (n : ℝ) ^ p)
    (hsize : ∀ᶠ n : ℕ in atTop, δ * (n : ℝ) ≤ (size n : ℝ)) :
    ∀ᶠ n : ℕ in atTop, ambient n ≤ (size n) ^ 6 := by
  have hdiverge : Tendsto (fun n : ℕ => (n : ℝ) ^ (6 - p)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hp)).comp tendsto_natCast_atTop_atTop
  have hlarge := tendsto_atTop.mp hdiverge (B / δ ^ (6 : ℕ))
  filter_upwards [hambient, hsize, hlarge, eventually_gt_atTop (0 : ℕ)] with n hN hm hB hn
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hscale : B ≤ δ ^ (6 : ℕ) * (n : ℝ) ^ (6 - p) := by
    rw [mul_comm]
    exact (div_le_iff₀ (pow_pos hδ _)).mp hB
  have hreal : (ambient n : ℝ) ≤ (size n : ℝ) ^ (6 : ℕ) := by
    calc
      (ambient n : ℝ) ≤ B * (n : ℝ) ^ p := hN
      _ ≤ (δ ^ (6 : ℕ) * (n : ℝ) ^ (6 - p)) * (n : ℝ) ^ p :=
        mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hnpos.le _)
      _ = (δ * (n : ℝ)) ^ (6 : ℕ) := by
        rw [mul_assoc, ← Real.rpow_add hnpos, sub_add_cancel, Real.rpow_ofNat, mul_pow]
      _ ≤ (size n : ℝ) ^ (6 : ℕ) := by
        exact pow_le_pow_left₀ (mul_nonneg hδ.le hnpos.le) hm _
  rw [← Nat.cast_pow] at hreal
  exact Nat.cast_le.mp hreal

end Jsp000726.PublicStructure
