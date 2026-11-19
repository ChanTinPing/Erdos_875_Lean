module

public import Jsp000726.LowerRankTwoPacking
public import Jsp000726.LowerEarlyCounts

@[expose] public section

namespace Jsp000726

open Finset

/-- Separation by `g` makes each interval shorter than `g` contain at most one carrier element. -/
theorem card_window_le_one_of_spacing {P : Finset ℕ} {g : ℕ}
    (hspacing : ∀ x ∈ P, ∀ z ∈ P, x < z → x + g ≤ z) (y : ℕ) :
    (P.filter fun x => x ≤ y ∧ y < x + g).card ≤ 1 := by
  apply card_le_one.mpr
  intro x hx z hz
  obtain ⟨hxP, hxlo, hxhi⟩ := mem_filter.mp hx
  obtain ⟨hzP, hzlo, hzhi⟩ := mem_filter.mp hz
  rcases lt_trichotomy x z with h | h | h
  · exact False.elim (not_le_of_gt hxhi ((hspacing x hxP z hzP h).trans hzlo))
  · exact h
  · exact False.elim (not_le_of_gt hzhi ((hspacing z hzP x hxP h).trans hxlo))

/-- Count a literal sum family with a fixed window multiplicity and track its actual
support and span, so it can subsequently be padded by different cardinalities. -/
theorem translated_family_with_span {a : ℕ → ℕ} {S T F P : Finset ℕ}
    {r q b V U g K : ℕ}
    (hST : Disjoint S T) (hF : F ⊆ sumLayer a S r) (hP : P ⊆ sumLayer a T q)
    (hspan : ∀ p ∈ P, b ≤ p ∧ p ≤ b + V)
    (hbudget : (∑ i ∈ S, a i) ≤ U)
    (hsmall : (∑ i ∈ S, a i) < g)
    (hwindow : ∀ y, (P.filter fun x => x ≤ y ∧ y < x + g).card ≤ K) :
    ∃ X : Finset ℕ, X ⊆ sumLayer a (S ∪ T) (r + q) ∧
      (∀ x ∈ X, b ≤ x ∧ x ≤ b + V + U) ∧ F.card * P.card ≤ K * X.card := by
  let f (p : ℕ × ℕ) := p.1 + p.2
  let X := (F ×ˢ P).image f
  have hX : X ⊆ sumLayer a (S ∪ T) (r + q) := by
    intro x hx
    obtain ⟨⟨y,z⟩, hp, rfl⟩ := mem_image.mp hx
    obtain ⟨hy, hz⟩ := mem_product.mp hp
    obtain ⟨Y, hY, hcY, hsY⟩ := mem_sumLayer.mp (hF hy)
    obtain ⟨Z, hZ, hcZ, hsZ⟩ := mem_sumLayer.mp (hP hz)
    have hd := hST.mono hY hZ
    exact mem_sumLayer.mpr ⟨Y ∪ Z, union_subset_union hY hZ,
      by rw [card_union_of_disjoint hd, hcY, hcZ], by rw [sum_union hd, hsY, hsZ]⟩
  have hFsum x (hx : x ∈ F) : x ≤ ∑ i ∈ S, a i := by
    obtain ⟨Z, hZ, _, hsZ⟩ := mem_sumLayer.mp (hF hx)
    exact hsZ ▸ sum_le_sum_of_subset hZ
  have hXspan : ∀ x ∈ X, b ≤ x ∧ x ≤ b + V + U := by
    intro x hx
    obtain ⟨⟨y,z⟩, hp, rfl⟩ := mem_image.mp hx
    obtain ⟨hy, hz⟩ := mem_product.mp hp
    have h := (hFsum y hy).trans hbudget
    have hz' := hspan z hz
    dsimp [f]
    omega
  refine ⟨X, hX, hXspan, ?_⟩
  rw [← card_product]
  have hf : ∀ p ∈ F ×ˢ P, f p ∈ X := fun p hp => mem_image_of_mem f hp
  apply card_le_mul_card_image_of_maps_to hf
  intro x _
  let Z := (F ×ˢ P).filter fun p => f p = x
  refine (card_le_card_of_injOn Prod.snd ?_ ?_).trans (hwindow x)
  · intro p hp
    obtain ⟨hp', he⟩ := mem_filter.mp (show p ∈ Z from hp)
    obtain ⟨hu, hv⟩ := mem_product.mp hp'
    have h := (hFsum p.1 hu).trans_lt hsmall
    dsimp [f] at he
    exact mem_filter.mpr ⟨hv, by omega⟩
  · intro p hp p' hp' he
    have hp₂ := (mem_filter.mp (show p ∈ Z from hp)).2
    have hp₂' := (mem_filter.mp (show p' ∈ Z from hp')).2
    dsimp [f] at hp₂ hp₂'
    exact Prod.ext (by omega) he

private theorem layer_mono_of_support_subset {a : ℕ → ℕ} {S T : Finset ℕ} {r : ℕ}
    (hST : S ⊆ T) : sumLayer a S r ⊆ sumLayer a T r := by
  intro x hx
  obtain ⟨W, hW, hr, hs⟩ := mem_sumLayer.mp hx
  exact mem_sumLayer.mpr ⟨W, hW.trans hST, hr, hs⟩

/-- A separated carrier gives a literal translated family with no loss of multiplicity. -/
theorem translated_family_of_spacing {a : ℕ → ℕ} {S T F P : Finset ℕ}
    {r q b V U g : ℕ}
    (hST : Disjoint S T) (hF : F ⊆ sumLayer a S r) (hP : P ⊆ sumLayer a T q)
    (hspan : ∀ p ∈ P, b ≤ p ∧ p ≤ b + V)
    (hbudget : (∑ i ∈ S, a i) ≤ U)
    (hsmall : (∑ i ∈ S, a i) < g)
    (hspacing : ∀ x ∈ P, ∀ z ∈ P, x < z → x + g ≤ z) :
    ∃ X : Finset ℕ, X ⊆ sumLayer a (S ∪ T) (r + q) ∧
      (∀ x ∈ X, b ≤ x ∧ x ≤ b + V + U) ∧ F.card * P.card ≤ X.card := by
  simpa only [one_mul] using
    translated_family_with_span hST hF hP hspan hbudget hsmall (card_window_le_one_of_spacing hspacing)

/-- Keep the larger of the low-spacing and chain-window translate families, with the
support and span common to both choices. -/
theorem rankTwo_inflated_family {a : ℕ → ℕ} {S₁ S₂ T W F₁ F₂ P : Finset ℕ}
    {r₁ r₂ q b V U g₁ g₂ K : ℕ}
    (hS₁ : S₁ ⊆ W) (hS₂ : S₂ ⊆ W) (hWT : Disjoint W T)
    (hF₁ : F₁ ⊆ sumLayer a S₁ r₁) (hF₂ : F₂ ⊆ sumLayer a S₂ r₂)
    (hP : P ⊆ sumLayer a T q) (hspan : ∀ p ∈ P, b ≤ p ∧ p ≤ b + V)
    (hbudget₁ : (∑ i ∈ S₁, a i) ≤ U) (hbudget₂ : (∑ i ∈ S₂, a i) ≤ U)
    (hsmall₁ : (∑ i ∈ S₁, a i) < g₁) (hsmall₂ : (∑ i ∈ S₂, a i) < g₂)
    (hsep : ∀ x ∈ P, ∀ z ∈ P, x < z → x + g₁ ≤ z)
    (hwin : ∀ y, (P.filter fun x => x ≤ y ∧ y < x + g₂).card ≤ K) :
    ∃ r : ℕ, ∃ X : Finset ℕ, X ⊆ sumLayer a (W ∪ T) r ∧
      (∀ x ∈ X, b ≤ x ∧ x ≤ b + V + U) ∧
      F₁.card * P.card ≤ X.card ∧ F₂.card * P.card ≤ K * X.card := by
  obtain ⟨X₁, hX₁, hspan₁, hcard₁⟩ :=
    translated_family_of_spacing (hWT.mono hS₁ Subset.rfl) hF₁ hP hspan hbudget₁ hsmall₁ hsep
  obtain ⟨X₂, hX₂, hspan₂, hcard₂⟩ :=
    translated_family_with_span (hWT.mono hS₂ Subset.rfl) hF₂ hP hspan hbudget₂ hsmall₂ hwin
  have hsub₁ := hX₁.trans (layer_mono_of_support_subset (union_subset_union hS₁ Subset.rfl))
  have hsub₂ := hX₂.trans (layer_mono_of_support_subset (union_subset_union hS₂ Subset.rfl))
  rcases le_total X₁.card X₂.card with h | h
  · exact ⟨_, X₂, hsub₂, hspan₂, hcard₁.trans h, hcard₂⟩
  · exact ⟨_, X₁, hsub₁, hspan₁, hcard₁, hcard₂.trans (Nat.mul_le_mul_left K h)⟩

/-- A finite family on at most half of the indices injects into the middle layer
by adding the same subset of the unused indices to every member. -/
theorem card_family_le_middleLayer {a : ℕ → ℕ} {S X : Finset ℕ} {r n : ℕ}
    (hS : S ⊆ range n) (hsize : S.card ≤ n / 2) (hX : X ⊆ sumLayer a S r) :
    X.card ≤ middleLayer a n := by
  classical
  by_cases hXe : X.Nonempty
  · obtain ⟨x, hx⟩ := hXe
    obtain ⟨Y, hY, hcardY, _⟩ := mem_sumLayer.mp (hX hx)
    have hrS : r ≤ S.card := hcardY ▸ card_le_card hY
    have hroom : n / 2 - r ≤ (range n \ S).card := by
      rw [card_sdiff_of_subset hS, card_range]
      have hdiv : n / 2 ≤ n := Nat.div_le_self _ _
      omega
    obtain ⟨Z, hZ, hcardZ⟩ := exists_subset_card_eq hroom
    have hSZ : Disjoint S Z := disjoint_sdiff.mono_right hZ
    let f (x : ℕ) := x + ∑ i ∈ Z, a i
    unfold middleLayer
    apply card_le_card_of_injOn f
    · intro y hy
      obtain ⟨U, hU, hUc, hUs⟩ := mem_sumLayer.mp (hX hy)
      have hd := hSZ.mono_left hU
      refine mem_sumLayer.mpr ⟨U ∪ Z, union_subset (hU.trans hS) (hZ.trans sdiff_subset), ?_, ?_⟩
      · rw [card_union_of_disjoint hd, hUc, hcardZ, Nat.add_sub_of_le (hrS.trans hsize)]
      · exact (sum_union hd).trans (by rw [hUs])
    · intro y _ z _ he
      exact Nat.add_right_cancel he
  · rw [not_nonempty_iff_eq_empty.mp hXe, card_empty]
    exact Nat.zero_le _

end Jsp000726
