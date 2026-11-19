module

public import Jsp000726.DyadicSixth
public import Jsp000726.LowerEarlyCounts

import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726

open Finset PublicStructure

/-- The span of an integer progression is attained by the sign-adapted corners. -/
theorem integerGAP_exists_corners_span (P : IntegerGAP) :
    ∃ lo ∈ P.carrier, ∃ hi ∈ P.carrier,
      hi - lo = ∑ i : Fin P.rank, |P.step i| * (P.length i : ℤ) := by
  let endpoint (i : Fin P.rank) : Fin (P.length i + 1) :=
    ⟨P.length i, Nat.lt_succ_self _⟩
  let x : P.Param := fun i => if 0 ≤ P.step i then 0 else endpoint i
  let y : P.Param := fun i => if 0 ≤ P.step i then endpoint i else 0
  have hmem (p : P.Param) : P.eval p ∈ P.carrier :=
    mem_image.mpr ⟨p, mem_univ _, rfl⟩
  refine ⟨P.eval x, hmem x, P.eval y, hmem y, ?_⟩
  unfold IntegerGAP.eval
  rw [add_sub_add_left_eq_sub, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  by_cases hs : 0 ≤ P.step i
  · simp [x, y, endpoint, hs, abs_of_nonneg hs, mul_comm]
  · simp [x, y, endpoint, hs, abs_of_neg (lt_of_not_ge hs)]
    ring

/-- Translating the progression to a finite subset-sum layer gives the total-prefix
weight as an upper bound on its span. -/
theorem integerGAP_span_le_prefixWeight {a : ℕ → ℕ} {n k : ℕ} {T : Finset ℕ}
    {P : IntegerGAP} {z : ℤ} (hT : T ⊆ range n)
    (htrans : ∀ x ∈ P.carrier, z + x ∈ (sumLayer a T k).map Nat.castEmbedding) :
    (∑ i : Fin P.rank, |P.step i| * (P.length i : ℤ)) ≤ (prefixWeight a n : ℤ) := by
  obtain ⟨lo, hlo, hi, hhi, hspan⟩ := integerGAP_exists_corners_span P
  obtain ⟨m, hm, hme⟩ := mem_map.mp (htrans lo hlo)
  obtain ⟨M, hM, hMe⟩ := mem_map.mp (htrans hi hhi)
  change (m : ℤ) = z + lo at hme
  change (M : ℤ) = z + hi at hMe
  have hMw : M ≤ prefixWeight a n := by
    obtain ⟨U, hU, _, eU⟩ := mem_sumLayer.mp hM
    rw [← eU]
    exact sum_le_sum_of_subset (hU.trans hT)
  have hr : (M : ℤ) ≤ (prefixWeight a n : ℤ) := by exact_mod_cast hMw
  have hm₀ : (0 : ℤ) ≤ m := Int.natCast_nonneg _
  rw [← hspan]
  omega

end Jsp000726
