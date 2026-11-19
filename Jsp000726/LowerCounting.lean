module

public import Jsp000726.LowerLayers
public import Mathlib.Data.Finset.Prod

@[expose] public section

namespace Jsp000726

open Finset

/-- The set of distinct subset-sum values on a finite support. -/
def sumValues (a : ℕ → ℕ) (s : Finset ℕ) : Finset ℕ :=
  s.powerset.image fun U => ∑ i ∈ U, a i

theorem mem_sumValues {a : ℕ → ℕ} {s : Finset ℕ} {x : ℕ} :
    x ∈ sumValues a s ↔ ∃ U : Finset ℕ, U ⊆ s ∧ (∑ i ∈ U, a i) = x := by
  simp [sumValues]

theorem sumValues_mono {a : ℕ → ℕ} {s t : Finset ℕ} (h : s ⊆ t) :
    sumValues a s ⊆ sumValues a t := by
  intro x hx
  obtain ⟨U, hU, heq⟩ := mem_sumValues.mp hx
  exact mem_sumValues.mpr ⟨U, hU.trans h, heq⟩

theorem sumLayer_subset_sumValues (a : ℕ → ℕ) (s : Finset ℕ) (r : ℕ) :
    sumLayer a s r ⊆ sumValues a s := by
  intro x hx
  obtain ⟨U, hU, _, heq⟩ := mem_sumLayer.mp hx
  exact mem_sumValues.mpr ⟨U, hU, heq⟩

theorem card_sumValues_le_sum_add_one (a : ℕ → ℕ) (s : Finset ℕ) :
    (sumValues a s).card ≤ (∑ i ∈ s, a i) + 1 := by
  have h : sumValues a s ⊆ range ((∑ i ∈ s, a i) + 1) := by
    intro x hx
    obtain ⟨U, hU, rfl⟩ := mem_sumValues.mp hx
    exact mem_range.mpr (Nat.lt_succ_iff.mpr (sum_le_sum_of_subset hU))
  simpa only [card_range] using card_le_card h

/-- Pad a fixed-cardinality layer by one subset of each available cardinality on a disjoint
support. The translates are pairwise disjoint by admissibility. -/
theorem card_sumLayer_mul_succ_le_sumValues {a : ℕ → ℕ} (ha : Admissible a)
    {R S : Finset ℕ} (hRS : Disjoint R S) (r : ℕ) :
    (sumLayer a R r).card * (S.card + 1) ≤ (sumValues a (R ∪ S)).card := by
  classical
  have hex (j : Fin (S.card + 1)) : ∃ V ⊆ S, V.card = j.val :=
    exists_subset_card_eq (Nat.lt_succ_iff.mp j.isLt)
  let V (j : Fin (S.card + 1)) := (hex j).choose
  have hV (j : Fin (S.card + 1)) : V j ⊆ S ∧ (V j).card = j.val := (hex j).choose_spec
  let f (p : sumLayer a R r × Fin (S.card + 1)) : ℕ := p.1.val + ∑ i ∈ V p.2, a i
  have hf (p : sumLayer a R r × Fin (S.card + 1)) : f p ∈ sumValues a (R ∪ S) := by
    obtain ⟨U, hU, _, hsum⟩ := mem_sumLayer.mp p.1.property
    have hd := hRS.mono hU (hV p.2).1
    refine mem_sumValues.mpr ⟨U ∪ V p.2, union_subset_union hU (hV p.2).1, ?_⟩
    rw [sum_union hd, hsum]
  let g (p : sumLayer a R r × Fin (S.card + 1)) : sumValues a (R ∪ S) := ⟨f p, hf p⟩
  have hg : Function.Injective g := by
    intro ⟨x,j⟩ ⟨y,k⟩ h
    have heq : x.val + (∑ i ∈ V j, a i) = y.val + (∑ i ∈ V k, a i) := congrArg Subtype.val h
    obtain ⟨U, hU, hcardU, hsumU⟩ := mem_sumLayer.mp x.property
    obtain ⟨W, hW, hcardW, hsumW⟩ := mem_sumLayer.mp y.property
    have hdU := hRS.mono hU (hV j).1
    have hdW := hRS.mono hW (hV k).1
    have hsums : (∑ i ∈ U ∪ V j, a i) = ∑ i ∈ W ∪ V k, a i := by
      rw [sum_union hdU, sum_union hdW, hsumU, hsumW]
      exact heq
    have hc := ha _ _ hsums
    rw [card_union_of_disjoint hdU, card_union_of_disjoint hdW, hcardU, hcardW, (hV j).2, (hV k).2] at hc
    have hjk : j = k := Fin.ext (Nat.add_left_cancel hc)
    subst k
    exact Prod.ext (Subtype.ext (Nat.add_right_cancel heq)) rfl
  simpa only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective g hg

private theorem large_term_translates {a : ℕ → ℕ} {H : ℕ} (hH : 0 < H) (S : Finset ℕ)
    (hh : ∀ i ∈ S, H ≤ a i) :
    ∃ T : Finset ℕ, T ⊆ sumValues a S ∧ T.card = S.card + 1 ∧
      ∀ x ∈ T, ∀ y ∈ T, x < y → x + H ≤ y := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨{0}, ?_, by simp, ?_⟩
      · intro x hx
        have : x = 0 := mem_singleton.mp hx
        subst x
        exact mem_sumValues.mpr ⟨∅, Subset.rfl, sum_empty⟩
      · intro x hx y hy hxy
        simp at hx hy
        omega
  | @insert i S hi ih =>
      obtain ⟨T, hT, hcard, hgaps⟩ := ih (fun j hj => hh j (mem_insert_of_mem hj))
      let w := ∑ j ∈ insert i S, a j
      have hle (x : ℕ) (hx : x ∈ T) : x + H ≤ w := by
        obtain ⟨U, hU, rfl⟩ := mem_sumValues.mp (hT hx)
        have hsum : (∑ j ∈ U, a j) ≤ ∑ j ∈ S, a j := sum_le_sum_of_subset hU
        have hiH := hh i (mem_insert_self _ _)
        rw [show w = a i + ∑ j ∈ S, a j from sum_insert hi]
        omega
      have hw : w ∉ T := fun h => (Nat.not_le_of_lt (by omega : w < w + H)) (hle w h)
      refine ⟨insert w T, ?_, ?_, ?_⟩
      · intro x hx
        rcases mem_insert.mp hx with rfl | hxT
        · exact mem_sumValues.mpr ⟨insert i S, Subset.rfl, rfl⟩
        · exact sumValues_mono (subset_insert _ _) (hT hxT)
      · rw [card_insert_of_notMem hw, card_insert_of_notMem hi, hcard]
      · intro x hx y hy hxy
        rcases mem_insert.mp hx with rfl | hxT
        · rcases mem_insert.mp hy with rfl | hyT
          · omega
          · have hy' := hle y hyT
            omega
        · rcases mem_insert.mp hy with rfl | hyT
          · exact hle x hxT
          · exact hgaps x hxT y hyT hxy

/-- Add separated cumulative sums of large terms to small subset sums. This is the
combinatorial threshold-shift estimate used in manuscript Lemma 3.1. -/
theorem card_sumValues_mul_succ_le_of_small_and_large {a : ℕ → ℕ} {R S : Finset ℕ}
    (hRS : Disjoint R S) {H : ℕ} (hH : 0 < H) (hR : (∑ i ∈ R, a i) < H)
    (hS : ∀ i ∈ S, H ≤ a i) :
    (sumValues a R).card * (S.card + 1) ≤ (sumValues a (R ∪ S)).card := by
  obtain ⟨T, hT, hcard, hgaps⟩ := large_term_translates hH S hS
  let f (p : sumValues a R × T) : ℕ := p.1.val + p.2.val
  have hf (p : sumValues a R × T) : f p ∈ sumValues a (R ∪ S) := by
    obtain ⟨U, hU, hsumU⟩ := mem_sumValues.mp p.1.property
    obtain ⟨V, hV, hsumV⟩ := mem_sumValues.mp (hT p.2.property)
    refine mem_sumValues.mpr ⟨U ∪ V, union_subset_union hU hV, ?_⟩
    rw [sum_union (hRS.mono hU hV), hsumU, hsumV]
  let g (p : sumValues a R × T) : sumValues a (R ∪ S) := ⟨f p, hf p⟩
  have hsmall (x : sumValues a R) : x.val < H := by
    obtain ⟨U, hU, hsum⟩ := mem_sumValues.mp x.property
    exact hsum ▸ (sum_le_sum_of_subset hU).trans_lt hR
  have hg : Function.Injective g := by
    intro ⟨x,j⟩ ⟨y,k⟩ h
    have heq : x.val + j.val = y.val + k.val := congrArg Subtype.val h
    have hjk : j = k := by
      apply Subtype.ext
      rcases lt_trichotomy j.val k.val with h | h | h
      · have hgap := hgaps _ j.property _ k.property h
        have hx := hsmall x
        omega
      · exact h
      · have hgap := hgaps _ k.property _ j.property h
        have hy := hsmall y
        omega
    subst k
    exact Prod.ext (Subtype.ext (Nat.add_right_cancel heq)) rfl
  simpa only [Fintype.card_prod, Fintype.card_coe, hcard] using Fintype.card_le_of_injective g hg

end Jsp000726
