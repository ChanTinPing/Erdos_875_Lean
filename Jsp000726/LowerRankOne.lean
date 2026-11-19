module

public import Jsp000726.LowerCounting
public import Jsp000726.LowerProgressions

@[expose] public section

namespace Jsp000726

open Finset

/-- Add two fixed-cardinality layers on disjoint supports and pad to a chosen larger
cardinality using indices outside both supports. -/
theorem sumLayer_translate_mem {a : ℕ → ℕ} {s t w : Finset ℕ} {r q k x y : ℕ}
    (hst : Disjoint s t) (hs : s ⊆ w) (ht : t ⊆ w)
    (hx : x ∈ sumLayer a s r) (hy : y ∈ sumLayer a t q)
    {V : Finset ℕ} (hV : V ⊆ w \ (s ∪ t)) (hVcard : V.card = k) :
    x + y + (∑ i ∈ V, a i) ∈ sumLayer a w (r + q + k) := by
  obtain ⟨X, hX, hXcard, hXsum⟩ := mem_sumLayer.mp hx
  obtain ⟨Y, hY, hYcard, hYsum⟩ := mem_sumLayer.mp hy
  have hXY : Disjoint X Y := hst.mono hX hY
  have hdV : Disjoint (X ∪ Y) V :=
    (disjoint_sdiff : Disjoint (s ∪ t) (w \ (s ∪ t))).mono (union_subset_union hX hY) hV
  refine mem_sumLayer.mpr ⟨X ∪ Y ∪ V, union_subset
    (union_subset (hX.trans hs) (hY.trans ht)) (hV.trans sdiff_subset), ?_, ?_⟩
  · rw [card_union_of_disjoint hdV, card_union_of_disjoint hXY, hXcard, hYcard, hVcard]
  · rw [sum_union hdV, sum_union hXY, hXsum, hYsum]

/-- Translating a small layer by a carrier that meets each length-`g` window at
most `K` times gives multiplicity at most `K`. Pad by a common disjoint subset. -/
theorem card_mul_le_sumLayer_of_bounded_translates {a : ℕ → ℕ} {s t w P : Finset ℕ}
    {r q k g K : ℕ} (hst : Disjoint s t) (hs : s ⊆ w) (ht : t ⊆ w)
    (hP : P ⊆ sumLayer a t q) (hsmall : (∑ i ∈ s, a i) < g)
    (hwindow : ∀ y, (P.filter fun x => x ≤ y ∧ y < x + g).card ≤ K)
    (hk : k ≤ (w \ (s ∪ t)).card) :
    (sumLayer a s r).card * P.card ≤ K * (sumLayer a w (r + q + k)).card := by
  obtain ⟨V, hV, hVcard⟩ := exists_subset_card_eq hk
  let v := ∑ i ∈ V, a i
  let f (p : ℕ × ℕ) := p.1 + p.2 + v
  have hf : ∀ p ∈ (sumLayer a s r) ×ˢ P, f p ∈ sumLayer a w (r + q + k) := by
    intro p hp
    obtain ⟨hx, hy⟩ := mem_product.mp hp
    exact sumLayer_translate_mem hst hs ht hx (hP hy) hV hVcard
  have hcard : ((sumLayer a s r) ×ˢ P).card ≤ K * (sumLayer a w (r + q + k)).card := by
    apply card_le_mul_card_image_of_maps_to hf
    intro y _
    set T := ((sumLayer a s r) ×ˢ P).filter (fun p => f p = y)
    refine (card_le_card_of_injOn Prod.snd ?_ ?_).trans (hwindow (y - v))
    · intro p hp
      have hp' : p ∈ T := hp
      have hxy : p.1 + p.2 + v = y := (mem_filter.mp hp').2
      obtain ⟨hx, hy⟩ := mem_product.mp (mem_filter.mp hp').1
      obtain ⟨X, hX, _, hsum⟩ := mem_sumLayer.mp hx
      have hbound : p.1 < g := hsum ▸ (sum_le_sum_of_subset hX).trans_lt hsmall
      exact mem_filter.mpr ⟨hy, by omega⟩
    · intro p hp p' hp' h
      have hm : p ∈ T := hp
      have hm' : p' ∈ T := hp'
      have hxy : p.1 + p.2 + v = y := (mem_filter.mp hm).2
      have hxy' : p'.1 + p'.2 + v = y := (mem_filter.mp hm').2
      exact Prod.ext (by omega) h
  simpa only [card_product] using hcard

/-- A separated family of translations multiplies the size of an early layer.
The same padding subset is used for the whole family. -/
theorem card_mul_le_sumLayer_of_separated_translates {a : ℕ → ℕ} {s t w P : Finset ℕ}
    {r q k g : ℕ} (hst : Disjoint s t) (hs : s ⊆ w) (ht : t ⊆ w)
    (hP : P ⊆ sumLayer a t q) (hsmall : (∑ i ∈ s, a i) < g)
    (hsep : ∀ x ∈ P, ∀ y ∈ P, x < y → x + g ≤ y)
    (hk : k ≤ (w \ (s ∪ t)).card) :
    (sumLayer a s r).card * P.card ≤ (sumLayer a w (r + q + k)).card := by
  have hw : ∀ y, (P.filter fun x => x ≤ y ∧ y < x + g).card ≤ 1 := by
    intro y
    apply card_le_one.mpr
    intro x hx z hz
    obtain ⟨hxP, hxl, hxu⟩ := mem_filter.mp hx
    obtain ⟨hzP, hzl, hzu⟩ := mem_filter.mp hz
    rcases lt_trichotomy x z with h | h | h
    · exact False.elim ((not_le_of_gt hxu) ((hsep _ hxP _ hzP h).trans hzl))
    · exact h
    · exact False.elim ((not_le_of_gt hzu) ((hsep _ hzP _ hxP h).trans hxl))
  simpa only [one_mul] using card_mul_le_sumLayer_of_bounded_translates hst hs ht hP hsmall hw hk

/-- An arithmetic progression in a fixed-cardinality layer gives the finite
rank-one lower estimate once the early layer fits inside one period. -/
theorem card_mul_le_sumLayer_of_progression {a : ℕ → ℕ} {s t w : Finset ℕ}
    {r q k b g L : ℕ} (hst : Disjoint s t) (hs : s ⊆ w) (ht : t ⊆ w) (hg : 0 < g)
    (hp : ProgressionInLayer a t q b g L) (hsmall : (∑ i ∈ s, a i) < g)
    (hk : k ≤ (w \ (s ∪ t)).card) :
    (sumLayer a s r).card * L ≤ (sumLayer a w (r + q + k)).card := by
  let P := (range L).image (fun j => b + g * j)
  have hmono : StrictMono (fun j : ℕ => b + g * j) := fun _ _ h =>
    Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left h hg) _
  have hcard : P.card = L := by
    simp [P, card_image_of_injective _ hmono.injective]
  have hP : P ⊆ sumLayer a t q := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
    exact mem_sumLayer.mpr (hp j (mem_range.mp hj))
  have hsep : ∀ x ∈ P, ∀ y ∈ P, x < y → x + g ≤ y := by
    intro x hx y hy hxy
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := mem_image.mp hy
    have hij : i + 1 ≤ j := by
      by_contra! hn
      exact (not_lt_of_ge (hmono.monotone (by omega))) hxy
    have hmul := Nat.mul_le_mul_left g hij
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega
  rw [← hcard]
  exact card_mul_le_sumLayer_of_separated_translates hst hs ht hP hsmall hsep hk

/-- The span of an arithmetic progression cannot exceed the total weight of its support. -/
theorem progression_span_le_weight {a : ℕ → ℕ} {t : Finset ℕ} {q b g L : ℕ}
    (hL : 0 < L) (hp : ProgressionInLayer a t q b g L) :
    g * (L - 1) ≤ ∑ i ∈ t, a i := by
  obtain ⟨X, hX, _, hsum⟩ := hp (L - 1) (by omega)
  exact (Nat.le_add_left _ _).trans ((hsum ▸ sum_le_sum_of_subset hX) :
    b + g * (L - 1) ≤ ∑ i ∈ t, a i)

end Jsp000726
