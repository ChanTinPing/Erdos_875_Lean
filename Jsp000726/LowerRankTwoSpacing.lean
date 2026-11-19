module

public import Jsp000726.LowerRankTwoPacking
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726

open Filter Finset

/-- Distinct-cardinality translates force the average spacing to grow as a power of the
ambient prefix length once the rank-two progression has cubic volume. -/
theorem rankTwo_spacing_power_lower {N V M m B D E : ℝ}
    (hN : 0 < N) (hM : 2 ≤ M) (hB : 0 < B) (hD : 0 < D) (hE : 0 < E)
    (hspan : M ≤ V + 1) (hvol : D * N ^ (3 : ℝ) ≤ M)
    (hprotect : E * V ^ (1 / B) ≤ m) (hpack : m * M ≤ 2 * V + 1) :
    (E / 3) * (D / 2) ^ (1 / B) * N ^ (3 / B) ≤ V / M := by
  have hM' : 0 < M := by linarith
  have hV : 1 ≤ V := by linarith
  have hhalf : (D / 2) * N ^ (3 : ℝ) ≤ V := by linarith
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ (D / 2) * N ^ (3 : ℝ)) hhalf (one_div_nonneg.mpr hB.le)
  rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hN.le _), ← Real.rpow_mul hN.le, mul_one_div] at hp
  have hm : (E / 3) * (D / 2) ^ (1 / B) * N ^ (3 / B) ≤ m / 3 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 3)).2
    calc
      _ = E * ((D / 2) ^ (1 / B) * N ^ (3 / B)) := by ring
      _ ≤ E * V ^ (1 / B) := mul_le_mul_of_nonneg_left hp hE.le
      _ ≤ m := hprotect
  apply hm.trans
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) hM').2
  linarith

/-- An arbitrary fixed spacing cutoff holds eventually, uniformly in the particular
rank-two progression chosen at each index. -/
theorem eventually_rankTwo_spacing_ge {B D E : ℝ} (hB : 0 < B) (hD : 0 < D) (hE : 0 < E) (R₀ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ {V M m : ℝ},
      M ≤ V + 1 → D * ((n : ℝ) + 1) ^ (3 : ℝ) ≤ M →
      E * V ^ (1 / B) ≤ m → m * M ≤ 2 * V + 1 → R₀ ≤ V / M := by
  have hN : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    refine tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ)) ?_ tendsto_natCast_atTop_atTop
    intro n
    exact le_add_of_nonneg_right zero_le_one
  have hN₃ := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3)).comp hN
  have hNβ := (tendsto_rpow_atTop (div_pos (by norm_num : (0 : ℝ) < 3) hB)).comp hN
  let K := (E / 3) * (D / 2) ^ (1 / B)
  have hK : 0 < K := by dsimp [K]; positivity
  filter_upwards [hN₃.eventually (eventually_ge_atTop (2 / D)), hNβ.eventually (eventually_ge_atTop (R₀ / K))]
    with n hn₃ hnβ V M m hspan hvol hprotect hpack
  change 2 / D ≤ ((n : ℝ) + 1) ^ (3 : ℝ) at hn₃
  change R₀ / K ≤ ((n : ℝ) + 1) ^ (3 / B) at hnβ
  have hM : 2 ≤ M := by
    have h := (div_le_iff₀ hD).1 hn₃
    rw [mul_comm] at h
    exact h.trans hvol
  have hh := rankTwo_spacing_power_lower (by positivity : 0 < (n : ℝ) + 1)
    hM hB hD hE hspan hvol hprotect hpack
  have h := (div_le_iff₀ hK).1 hnβ
  rw [mul_comm] at h
  exact h.trans hh

/-- Integer carriers of diameter `V` contain at most `V+1` values. -/
theorem card_int_le_diameter_add_one {P : Finset ℤ} {lo hi : ℤ}
    (h : ∀ x ∈ P, lo ≤ x ∧ x ≤ hi) : (P.card : ℤ) ≤ max 0 (hi - lo + 1) := by
  have hh := card_le_card (show P ⊆ Icc lo hi from fun _ hx => mem_Icc.mpr (h _ hx))
  rw [Int.card_Icc] at hh
  omega

end Jsp000726
