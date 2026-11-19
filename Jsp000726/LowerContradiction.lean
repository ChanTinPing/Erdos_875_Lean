module

public import Jsp000726.LowerBigGaps
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726

open Filter Finset

/-- Once the preceding prefix weight grows with strictly larger exponent, the
large-gap lemma contradicts any eventual upper bound on the gaps. -/
theorem not_eventual_gap_cap_of_prefix_growth {a : ℕ → ℕ} (hmono : StrictMono a)
    (hpos : ∀ i, 0 < a i) (ha : Admissible a) {c u C : ℝ} (hcu : c < u) (hC : 0 < C)
    (hweight : ∀ᶠ n : ℕ in atTop, C * (n + 1 : ℝ) ^ u ≤
      ((∑ i ∈ range (n - 2), a i : ℕ) : ℝ)) :
    ¬ (∀ᶠ n : ℕ in atTop, (gap a n : ℝ) ≤ (n + 1 : ℝ) ^ c) := by
  intro hgap
  have hbase : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ)) ?_ tendsto_natCast_atTop_atTop
    intro n
    exact le_add_of_nonneg_right zero_le_one
  have hpower : Tendsto (fun n : ℕ => (n + 1 : ℝ) ^ (u - c)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hcu)).comp hbase
  have hbig := hpower.eventually (eventually_gt_atTop (4 / C))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hgap.and (hweight.and hbig))
  obtain ⟨n, hn, hlarge⟩ := large_gaps_often hmono hpos ha N
  obtain ⟨hcap, hW, hP⟩ := hN n hn
  have hX : 0 < (n + 1 : ℝ) := by positivity
  have heq : (n + 1 : ℝ) ^ u = (n + 1 : ℝ) ^ (u - c) * (n + 1 : ℝ) ^ c := by
    rw [← Real.rpow_add hX, sub_add_cancel]
  have hlt : 4 * (n + 1 : ℝ) ^ c < C * (n + 1 : ℝ) ^ u := by
    have hscale : 4 < (n + 1 : ℝ) ^ (u - c) * C := (div_lt_iff₀ hC).mp hP
    rw [heq, ← mul_assoc, mul_comm C]
    exact mul_lt_mul_of_pos_right hscale (Real.rpow_pos_of_pos hX _)
  have hlarge' : ((∑ i ∈ range (n - 2), a i : ℕ) : ℝ) < 4 * (gap a n : ℝ) := by
    exact_mod_cast hlarge
  linarith only [hlarge', hcap, hW, hlt]

/-- A lower bound on ordinary prefix weights also applies to the shortened prefix
used in the large-gap lemma, with a fixed loss in its constant. -/
theorem eventual_shortened_prefix_growth {a : ℕ → ℕ} {u C : ℝ} (hu : 0 ≤ u) (hC : 0 < C)
    (hweight : ∀ᶠ n : ℕ in atTop, C * (n + 1 : ℝ) ^ u ≤
      ((∑ i ∈ range n, a i : ℕ) : ℝ)) :
    ∀ᶠ n : ℕ in atTop, (C / (2 : ℝ) ^ u) * (n + 1 : ℝ) ^ u ≤
      ((∑ i ∈ range (n - 2), a i : ℕ) : ℝ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hweight
  apply eventually_atTop.mpr
  refine ⟨N + 5, fun n hn => ?_⟩
  have hhalf : (n + 1 : ℝ) / 2 ≤ ((n - 2 : ℕ) : ℝ) + 1 := by
    apply (div_le_iff₀ (show (0 : ℝ) < 2 by norm_num)).2
    exact_mod_cast (by omega : n + 1 ≤ (n - 2 + 1) * 2)
  calc
    _ = C * ((n + 1 : ℝ) / 2) ^ u := by
      rw [Real.div_rpow (by positivity) (by norm_num)]
      ring
    _ ≤ C * (((n - 2 : ℕ) : ℝ) + 1) ^ u := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hhalf hu) hC.le
    _ ≤ _ := hN (n - 2) (by omega)

end Jsp000726
