module

public import Jsp000726.LowerEarlyCounts
public import Jsp000726.LowerRankOne
public import Mathlib.Data.Fintype.EquivFin

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

namespace Jsp000726

open Finset

/-- A progression with a protected early prefix forces at least one residue per
pair of a largest-layer value and a padding cardinality. -/
theorem largestLayer_mul_le_of_protected_prefix {a : ℕ → ℕ} (ha : Admissible a)
    {j m : ℕ} (hjm : j ≤ m) {t : Finset ℕ} (hst : Disjoint (range m) t)
    {q b g L : ℕ} (hg : 0 < g) (hL : 0 < L)
    (hp : ProgressionInLayer a t q b g L)
    (hspan : prefixWeight a m ≤ g * (L - 1)) (hsmall : prefixWeight a j < g) :
    largestLayer a j * (m - j + 1) ≤ g := by
  classical
  obtain ⟨r, _, hr⟩ := exists_layer_card_eq_largestLayer a j
  let S := range m \ range j
  have hcard : S.card = m - j := by
    rw [show S = range m \ range j from rfl, card_sdiff_of_subset (range_mono hjm),
      card_range, card_range]
  let e := (Finset.equivFinOfCardEq hr).symm
  have hxe (x : Fin (largestLayer a j)) :
      ∃ U : Finset ℕ, U ⊆ range j ∧ U.card = r ∧ (∑ i ∈ U, a i) = (e x).val :=
    mem_sumLayer.mp (e x).property
  choose F hF using hxe
  have hpad (y : Fin (m - j + 1)) : ∃ V ⊆ S, V.card = y.val :=
    exists_subset_card_eq (by rw [hcard]; omega)
  choose P hP using hpad
  have hRS : Disjoint (range j) S := disjoint_sdiff
  apply card_mul_card_le_of_progression ha hst hRS (range_mono hjm) sdiff_subset
    hg hL hp hspan F P (fun x => (hF x).1) (fun y => (hP y).1)
    (fun x => (hF x).2.1) (fun y => (hP y).2)
  · intro x
    exact (sum_le_sum_of_subset (hF x).1).trans_lt hsmall
  · intro x y heq
    apply e.injective
    exact Subtype.ext ((hF x).2.2.symm.trans (heq.trans (hF y).2.2))

/-- If the early prefix and progression together use at most half the indices,
the finite rank-one estimate pads exactly to the middle layer. -/
theorem largestLayer_mul_progression_le_middleLayer {a : ℕ → ℕ} {n j : ℕ}
    {t : Finset ℕ} (ht : t ⊆ range n) (hst : Disjoint (range j) t)
    (hsize : j + t.card ≤ n / 2) {q b g L : ℕ} (hg : 0 < g) (hL : 0 < L)
    (hp : ProgressionInLayer a t q b g L) (hsmall : prefixWeight a j < g) :
    largestLayer a j * L ≤ middleLayer a n := by
  obtain ⟨r, hr, hrs⟩ := exists_layer_card_eq_largestLayer a j
  have hq : q ≤ t.card := by
    obtain ⟨U, hU, hUcard, _⟩ := hp 0 hL
    exact hUcard ▸ card_le_card hU
  have hsubset : range j ⊆ range n := range_mono (by omega)
  let k := n / 2 - (r + q)
  have hk : k ≤ (range n \ (range j ∪ t)).card := by
    rw [card_sdiff_of_subset (union_subset hsubset ht), card_union_of_disjoint hst,
      card_range, card_range]
    dsimp [k]
    omega
  have h := card_mul_le_sumLayer_of_progression (r := r) hst hsubset ht hg hp hsmall hk
  rw [hrs, show r + q + k = n / 2 by dsimp [k]; omega] at h
  exact h

/-- Choose a protected prefix whose size is controlled from below by the span.
The cap at `n/4` ensures disjointness from the later paired support. -/
theorem exists_protected_prefix_of_span {a : ℕ → ℕ} (hpos : ∀ i, 0 < a i)
    {n V : ℕ} {C B : ℝ} (hC : 0 < C) (hB : 0 < B)
    (hpref : ∀ j, (prefixWeight a j : ℝ) ≤ C * (j : ℝ) ^ B)
    (hV : (V : ℝ) ≤ C * (n : ℝ) ^ B) :
    ∃ m ≤ n / 4, prefixWeight a m ≤ V ∧
      (V : ℝ) ^ (1 / B) / (4 * C ^ (1 / B)) ≤ (m : ℝ) + 1 := by
  let m := min (prefixAt a V) (n / 4)
  have hmat : m ≤ prefixAt a V := min_le_left _ _
  have hmn : m ≤ n / 4 := min_le_right _ _
  have hweight := (prefixWeight_mono a hmat).trans (prefixWeight_at_le a V)
  refine ⟨m, hmn, hweight, ?_⟩
  have hroot {k : ℕ} (h : (V : ℝ) ≤ C * (k : ℝ) ^ B) :
      (V : ℝ) ^ (1 / B) / C ^ (1 / B) ≤ (k : ℝ) := by
    have h' : (V : ℝ) / C ≤ (k : ℝ) ^ B := by
      rw [div_le_iff₀ hC, mul_comm]
      exact h
    have h'' := Real.rpow_le_rpow (div_nonneg (Nat.cast_nonneg V) hC.le) h'
      (one_div_nonneg.mpr hB.le)
    rw [Real.div_rpow (Nat.cast_nonneg V) hC.le, one_div,
      Real.rpow_rpow_inv (Nat.cast_nonneg k) hB.ne'] at h''
    simpa only [one_div] using h''
  rw [mul_comm (4 : ℝ), ← div_div]
  by_cases h : prefixAt a V ≤ n / 4
  · have hm : m = prefixAt a V := min_eq_left h
    have hpv := prefixAt_lt_prefixWeight_succ hpos V
    rw [← hm] at hpv
    have hpv' : (V : ℝ) ≤ (prefixWeight a (m + 1) : ℝ) := by exact_mod_cast hpv.le
    have hr := hroot (hpv'.trans (hpref _))
    rw [Nat.cast_add, Nat.cast_one] at hr
    exact (div_le_div_of_nonneg_right hr (by norm_num)).trans (by linarith only [show (0 : ℝ) ≤ m from Nat.cast_nonneg m])
  · have hm : m = n / 4 := min_eq_right (Nat.le_of_not_ge h)
    have hfloor : n ≤ 4 * (m + 1) := by rw [hm]; omega
    have hfloor' : (n : ℝ) ≤ 4 * ((m : ℝ) + 1) := by exact_mod_cast hfloor
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
      ((hroot hV).trans (hfloor'.trans_eq (mul_comm _ _)))

end Jsp000726
