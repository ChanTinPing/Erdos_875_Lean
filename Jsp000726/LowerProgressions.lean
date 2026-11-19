module

public import Jsp000726.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.ModEq

@[expose] public section

namespace Jsp000726

open Finset

/-- An ordinary progression whose values are represented by subsets of a common cardinality. -/
def ProgressionInLayer (a : ℕ → ℕ) (s : Finset ℕ) (r b g L : ℕ) : Prop :=
  ∀ j < L, ∃ T : Finset ℕ, T ⊆ s ∧ T.card = r ∧ (∑ i ∈ T, a i) = b + g * j

/-- A progression in a disjoint support protects cardinality information in prefix residues. -/
theorem cardinality_eq_of_modEq_of_progression {a : ℕ → ℕ} (ha : Admissible a)
    {s t : Finset ℕ} (hst : Disjoint s t) {r b g L : ℕ} (hg : 0 < g) (hL : 0 < L)
    (hprog : ProgressionInLayer a t r b g L)
    (hspan : (∑ i ∈ s, a i) ≤ g * (L - 1)) {U V : Finset ℕ} (hU : U ⊆ s) (hV : V ⊆ s)
    (hmod : (∑ i ∈ U, a i) ≡ (∑ i ∈ V, a i) [MOD g]) : U.card = V.card := by
  have step {C D : Finset ℕ} (hC : C ⊆ s) (hD : D ⊆ s)
      (hCD : (∑ i ∈ C, a i) ≤ ∑ i ∈ D, a i)
      (hm : (∑ i ∈ C, a i) ≡ (∑ i ∈ D, a i) [MOD g]) : C.card = D.card := by
    obtain ⟨j, hj⟩ := (Nat.modEq_iff_dvd' hCD).mp hm
    have hsub : g * j ≤ g * (L - 1) := by
      rw [← hj]
      exact (Nat.sub_le _ _).trans ((sum_le_sum_of_subset hD).trans hspan)
    have hjL : j < L := by
      have hjle := Nat.le_of_mul_le_mul_left hsub hg
      omega
    obtain ⟨P, hP, hPcard, hPsum⟩ := hprog 0 hL
    obtain ⟨Q, hQ, hQcard, hQsum⟩ := hprog j hjL
    have hCQ := hst.mono hC hQ
    have hDP := hst.mono hD hP
    have heq : (∑ i ∈ C ∪ Q, a i) = ∑ i ∈ D ∪ P, a i := by
      rw [sum_union hCQ, sum_union hDP, hQsum, hPsum, Nat.mul_zero, Nat.add_zero]
      omega
    have hcard := ha _ _ heq
    rw [card_union_of_disjoint hCQ, card_union_of_disjoint hDP, hPcard, hQcard] at hcard
    omega
  rcases le_total (∑ i ∈ U, a i) (∑ i ∈ V, a i) with h | h
  · exact step hU hV h hmod
  · exact (step hV hU h hmod.symm).symm

/-- Distinct cardinality shifts of a small layer give disjoint families of protected residues. -/
theorem card_mul_card_le_of_progression {a : ℕ → ℕ} (ha : Admissible a)
    {s t R S : Finset ℕ} (hst : Disjoint s t) (hRS : Disjoint R S) (hR : R ⊆ s) (hS : S ⊆ s)
    {r b g L : ℕ} (hg : 0 < g) (hL : 0 < L) (hprog : ProgressionInLayer a t r b g L)
    (hspan : (∑ i ∈ s, a i) ≤ g * (L - 1))
    {m k c : ℕ} (F : Fin m → Finset ℕ) (P : Fin k → Finset ℕ)
    (hF : ∀ x, F x ⊆ R) (hP : ∀ y, P y ⊆ S)
    (hFcard : ∀ x, (F x).card = c) (hPcard : ∀ y, (P y).card = y.val)
    (hFsmall : ∀ x, (∑ i ∈ F x, a i) < g)
    (hFinj : Function.Injective fun x => ∑ i ∈ F x, a i) : m * k ≤ g := by
  have hdis (x : Fin m) (y : Fin k) : Disjoint (F x) (P y) := hRS.mono (hF x) (hP y)
  have hsub (x : Fin m) (y : Fin k) : F x ∪ P y ⊆ s :=
    union_subset ((hF x).trans hR) ((hP y).trans hS)
  let f : Fin m × Fin k → Fin g := fun z =>
    ⟨(∑ i ∈ F z.1 ∪ P z.2, a i) % g, Nat.mod_lt _ hg⟩
  have hfinj : Function.Injective f := by
    intro ⟨x, y⟩ ⟨x', y'⟩ heq
    have hm : (∑ i ∈ F x ∪ P y, a i) ≡ (∑ i ∈ F x' ∪ P y', a i) [MOD g] :=
      congrArg Fin.val heq
    have hcard := cardinality_eq_of_modEq_of_progression ha hst hg hL hprog hspan
      (hsub x y) (hsub x' y') hm
    rw [card_union_of_disjoint (hdis x y), card_union_of_disjoint (hdis x' y'), hFcard, hFcard,
      hPcard, hPcard] at hcard
    have hy : y = y' := Fin.ext (by omega)
    subst y'
    rw [sum_union (hdis x y), sum_union (hdis x' y)] at hm
    have hm' := Nat.ModEq.add_right_cancel' (∑ i ∈ P y, a i) hm
    change (∑ i ∈ F x, a i) % g = (∑ i ∈ F x', a i) % g at hm'
    rw [Nat.mod_eq_of_lt (hFsmall x), Nat.mod_eq_of_lt (hFsmall x')] at hm'
    exact Prod.ext (hFinj hm') rfl
  simpa only [Fintype.card_prod, Fintype.card_fin] using Fintype.card_le_of_injective f hfinj

end Jsp000726
