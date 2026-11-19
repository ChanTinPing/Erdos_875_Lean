module

public import Jsp000726.LowerRankOne

@[expose] public section

namespace Jsp000726

open Finset

/-- A short numerical window meets only one chain, so it has at most the largest chain size. -/
theorem card_window_le_of_separated_chains {ι : Type*} [DecidableEq ι]
    {P : Finset ℕ} {g K : ℕ} (label : ℕ → ι)
    (hsize : ∀ i, (P.filter fun x => label x = i).card ≤ K)
    (hsep : ∀ x ∈ P, ∀ z ∈ P, label x ≠ label z → x + g ≤ z ∨ z + g ≤ x)
    (y : ℕ) : (P.filter fun x => x ≤ y ∧ y < x + g).card ≤ K := by
  let Q := P.filter fun x => x ≤ y ∧ y < x + g
  change Q.card ≤ K
  by_cases hQ : Q.Nonempty
  · obtain ⟨x, hx⟩ := hQ
    obtain ⟨hxP, hxlo, hxhi⟩ := mem_filter.mp (show x ∈ Q from hx)
    refine (card_le_card ?_).trans (hsize (label x))
    intro z hz
    obtain ⟨hzP, hzlo, hzhi⟩ := mem_filter.mp (show z ∈ Q from hz)
    refine mem_filter.mpr ⟨hzP, ?_⟩
    by_contra hdiff
    rcases hsep _ hzP _ hxP hdiff with h | h <;> omega
  · rw [not_nonempty_iff_eq_empty.mp hQ, card_empty]
    exact Nat.zero_le K

/-- Distinct-cardinality padding of a given family forces its combined span to grow. -/
theorem card_mul_succ_le_span_of_layer {a : ℕ → ℕ} (ha : Admissible a)
    {X R S : Finset ℕ} {r b W V : ℕ}
    (hRS : Disjoint R S) (hX : X ⊆ sumLayer a R r)
    (hspan : ∀ x ∈ X, b ≤ x ∧ x ≤ b + W)
    (hbudget : (∑ i ∈ S, a i) ≤ V) :
    X.card * (S.card + 1) ≤ W + V + 1 := by
  classical
  have hex (j : Fin (S.card + 1)) : ∃ U ⊆ S, U.card = j.val :=
    exists_subset_card_eq (Nat.lt_succ_iff.mp j.isLt)
  let U (j : Fin (S.card + 1)) := (hex j).choose
  have hU (j : Fin (S.card + 1)) : U j ⊆ S ∧ (U j).card = j.val := (hex j).choose_spec
  let f (p : X × Fin (S.card + 1)) : ℕ := p.1.val - b + ∑ i ∈ U p.2, a i
  have hbound (p : X × Fin (S.card + 1)) : f p < W + V + 1 := by
    have hx := (hspan p.1.val p.1.property).2
    have hu := (sum_le_sum_of_subset (hU p.2).1).trans hbudget
    dsimp [f]
    omega
  let g (p : X × Fin (S.card + 1)) : Fin (W + V + 1) := ⟨f p, hbound p⟩
  have hg : Function.Injective g := by
    intro ⟨x, j⟩ ⟨y, k⟩ h
    have he := congrArg Fin.val h
    change x.val - b + (∑ i ∈ U j, a i) = y.val - b + (∑ i ∈ U k, a i) at he
    have hx := (hspan x.val x.property).1
    have hy := (hspan y.val y.property).1
    have heq : x.val + (∑ i ∈ U j, a i) = y.val + (∑ i ∈ U k, a i) := by omega
    obtain ⟨T, hT, hcT, hsT⟩ := mem_sumLayer.mp (hX x.property)
    obtain ⟨T', hT', hcT', hsT'⟩ := mem_sumLayer.mp (hX y.property)
    have hdT := hRS.mono hT (hU j).1
    have hdT' := hRS.mono hT' (hU k).1
    have hfinite : (∑ i ∈ T ∪ U j, a i) = ∑ i ∈ T' ∪ U k, a i := by
      rw [sum_union hdT, sum_union hdT', hsT, hsT']
      exact heq
    have hcard := ha _ _ hfinite
    rw [card_union_of_disjoint hdT, card_union_of_disjoint hdT', hcT, hcT',
      (hU j).2, (hU k).2] at hcard
    have hjk : j = k := Fin.ext (Nat.add_left_cancel hcard)
    subst k
    exact Prod.ext (Subtype.ext (Nat.add_right_cancel heq)) rfl
  simpa only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin] using
    Fintype.card_le_of_injective g hg

end Jsp000726
