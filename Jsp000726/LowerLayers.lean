module

public import Jsp000726.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Powerset

@[expose] public section

namespace Jsp000726

open Finset

/-- Distinct sums of `r` terms with indices in the finite set `s`. -/
def sumLayer (a : ℕ → ℕ) (s : Finset ℕ) (r : ℕ) : Finset ℕ :=
  (s.powersetCard r).image fun U => ∑ i ∈ U, a i

theorem mem_sumLayer {a : ℕ → ℕ} {s : Finset ℕ} {r x : ℕ} :
    x ∈ sumLayer a s r ↔ ∃ U : Finset ℕ, U ⊆ s ∧ U.card = r ∧ (∑ i ∈ U, a i) = x := by
  constructor
  · intro hx
    obtain ⟨U, hU, hs⟩ := mem_image.mp hx
    exact ⟨U, (mem_powersetCard.mp hU).1, (mem_powersetCard.mp hU).2, hs⟩
  · rintro ⟨U, hU, hr, hs⟩
    exact mem_image.mpr ⟨U, mem_powersetCard.mpr ⟨hU, hr⟩, hs⟩

private theorem layer_mono {a : ℕ → ℕ} {s t : Finset ℕ} (hst : s ⊆ t) (r : ℕ) :
    sumLayer a s r ⊆ sumLayer a t r := by
  intro x hx
  obtain ⟨U, hU, hc, hs⟩ := mem_sumLayer.mp hx
  exact mem_sumLayer.mpr ⟨U, hU.trans hst, hc, hs⟩

private theorem sum_le_sum_upper_indices {a : ℕ → ℕ} (ha : Monotone a) {n r : ℕ} (hr : r ≤ n)
    {U : Finset ℕ} (hU : U ⊆ range n) (hcard : U.card = r) :
    (∑ i ∈ U, a i) ≤ ∑ i ∈ range n \ range (n - r), a i := by
  let T := range n \ range (n - r)
  have hTcard : T.card = r := by
    dsimp [T]
    rw [card_sdiff_of_subset (range_mono (Nat.sub_le n r)), card_range, card_range]
    omega
  have hsubcard : (U \ T).card = (T \ U).card :=
    card_sdiff_eq_card_sdiff_iff.mpr (hcard.trans hTcard.symm)
  have hlow : ∀ i ∈ U \ T, i < n - r := by
    intro i hi
    have hiU := (mem_sdiff.mp hi).1
    have hiT := (mem_sdiff.mp hi).2
    by_contra! his
    apply hiT
    exact mem_sdiff.mpr ⟨hU hiU, fun hir => (not_lt_of_ge his) (mem_range.mp hir)⟩
  have hu : (∑ i ∈ U \ T, a i) ≤ ∑ _i ∈ U \ T, a (n - r) := by
    exact sum_le_sum fun i hi => ha (hlow i hi).le
  have ht : (∑ _i ∈ T \ U, a (n - r)) ≤ ∑ i ∈ T \ U, a i := by
    refine sum_le_sum fun i hi => ha ?_
    have h := (mem_sdiff.mp ((mem_sdiff.mp hi).1)).2
    exact Nat.le_of_not_gt fun hlt => h (mem_range.mpr hlt)
  simp only [sum_const, nsmul_eq_mul] at hu ht
  have hu' : (∑ i ∈ U \ T, a i) ≤ ∑ i ∈ T \ U, a i := by
    rw [hsubcard] at hu
    exact hu.trans ht
  have hUeq : (∑ i ∈ U \ T, a i) + (∑ i ∈ U ∩ T, a i) = ∑ i ∈ U, a i := by
    rw [← sum_union]
    · congr 1
      ext i
      by_cases hi : i ∈ T <;> simp [hi]
    · exact Finset.disjoint_left.mpr fun _ h hh => (mem_sdiff.mp h).2 (mem_inter.mp hh).2
  have hTeq : (∑ i ∈ T \ U, a i) + (∑ i ∈ U ∩ T, a i) = ∑ i ∈ T, a i := by
    rw [← sum_union]
    · congr 1
      ext i
      by_cases hi : i ∈ U <;> simp [hi]
    · exact Finset.disjoint_left.mpr fun _ h hh => (mem_sdiff.mp h).2 (mem_inter.mp hh).1
  change (∑ i ∈ U, a i) ≤ ∑ i ∈ T, a i
  omega

private theorem layer_step {a : ℕ → ℕ} (ha : StrictMono a) {n r : ℕ} (hr : r ≤ n) :
    (sumLayer a (range n) r).card + r ≤ (sumLayer a (range (n + 1)) r).card := by
  let T := range n \ range (n - r)
  let W := insert n T
  let f (i : ℕ) := ∑ j ∈ W.erase i, a j
  have hTsub : T ⊆ range n := sdiff_subset
  have hnT : n ∉ T := fun h => (not_lt_of_ge le_rfl) (mem_range.mp (hTsub h))
  have hTcard : T.card = r := by
    dsimp [T]
    rw [card_sdiff_of_subset (range_mono (Nat.sub_le n r)), card_range, card_range]
    omega
  have hWcard : W.card = r + 1 := by simpa only [W, card_insert_of_notMem hnT] using congrArg (·+1) hTcard
  have hWsub : W ⊆ range (n + 1) := by
    intro i hi
    rcases mem_insert.mp hi with rfl | hiT
    · exact mem_range.mpr (Nat.lt_succ_self _)
    · exact mem_range.mpr ((mem_range.mp (hTsub hiT)).trans (Nat.lt_succ_self n))
  have hsumW : (∑ i ∈ W, a i) = a n + ∑ i ∈ T, a i := sum_insert hnT
  have hf {i : ℕ} (hi : i ∈ T) : f i + a i = ∑ j ∈ W, a j :=
    sum_erase_add W a (mem_insert_of_mem hi)
  have hfinj : (T : Set ℕ).InjOn f := by
    intro i hi j hj heq
    apply ha.injective
    have hi' := hf hi
    have hj' := hf hj
    omega
  have hnew : T.image f ⊆ sumLayer a (range (n + 1)) r := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    have hiW : i ∈ W := mem_insert_of_mem hi
    have hcard : (W.erase i).card = r := by rw [card_erase_of_mem hiW, hWcard]; omega
    exact mem_sumLayer.mpr ⟨W.erase i, (erase_subset i W).trans hWsub, hcard, rfl⟩
  have hdis : Disjoint (sumLayer a (range n) r) (T.image f) := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨U, hU, hcard, hsum⟩ := mem_sumLayer.mp hx
    obtain ⟨i, hi, hfx⟩ := mem_image.mp hx'
    have hle := sum_le_sum_upper_indices ha.monotone hr hU hcard
    have hlt := ha (mem_range.mp (hTsub hi))
    have hfi := hf hi
    change (∑ i ∈ U, a i) ≤ ∑ i ∈ T, a i at hle
    omega
  have hold := layer_mono (a := a) (range_mono (Nat.le_succ n)) r
  have hcount := card_le_card (union_subset hold hnew)
  rwa [card_union_of_disjoint hdis, card_image_of_injOn hfinj, hTcard] at hcount

/-- The elementary lower bound on the size of any fixed-cardinality subset-sum layer. -/
theorem card_sumLayer_ge {a : ℕ → ℕ} (ha : StrictMono a) {n r : ℕ} (hr : r ≤ n) :
    1 + r * (n - r) ≤ (sumLayer a (range n) r).card := by
  induction n with
  | zero =>
      have : r = 0 := by omega
      subst r
      simp [sumLayer]
  | succ n ih =>
      rcases Nat.lt_or_eq_of_le hr with hlt | heq
      · have hrn : r ≤ n := by omega
        have hstep := layer_step ha hrn
        have hsub : n + 1 - r = (n - r) + 1 := by omega
        rw [hsub, Nat.mul_succ]
        have hi := ih hrn
        omega
      · subst r
        have hmem : (∑ i ∈ range (n + 1), a i) ∈ sumLayer a (range (n + 1)) (n + 1) :=
          mem_sumLayer.mpr ⟨range (n + 1), Subset.rfl, card_range _, rfl⟩
        simpa only [Nat.sub_self, Nat.mul_zero, Nat.add_zero] using (Nat.succ_le_iff.mpr (card_pos.mpr ⟨_, hmem⟩))

/-- Admissibility makes the sum layers at distinct cardinalities disjoint. -/
theorem disjoint_sumLayer_of_ne {a : ℕ → ℕ} (ha : Admissible a) (s : Finset ℕ)
    {r q : ℕ} (hrq : r ≠ q) : Disjoint (sumLayer a s r) (sumLayer a s q) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨U, _, hu, hux⟩ := mem_sumLayer.mp hx
  obtain ⟨V, _, hv, hvx⟩ := mem_sumLayer.mp hy
  exact hrq (hu.symm.trans ((ha _ _ (hux.trans hvx.symm)).trans hv))

end Jsp000726
