module

public import Jsp000726.LowerEarlyCounts
public import Jsp000726.LowerPairing

import Mathlib.Tactic.NormNum

@[expose] public section

namespace Jsp000726

open Finset

/-- Translate an integer carrier into an existing fixed-cardinality layer, then pad
every value with the same disjoint set of extra terms to reach the middle layer. -/
theorem card_le_middleLayer_of_integer_translate
    {a : ℕ → ℕ} {n k : ℕ} {T : Finset ℕ} {P : Finset ℤ} {z : ℤ}
    (hT : T ⊆ range n) (hk : k ≤ n / 2) (hpad : n / 2 - k ≤ ((range n) \ T).card)
    (hP : ∀ x ∈ P, z + x ∈ (sumLayer a T k).map Nat.castEmbedding) :
    P.card ≤ middleLayer a n := by
  let f : ℤ ↪ ℤ := ⟨(z + ·), fun _ _ h => add_left_cancel h⟩
  have hf : P.map f ⊆ (sumLayer a T k).map Nat.castEmbedding := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
    exact hP x hx
  have hCount : P.card ≤ (sumLayer a T k).card := by
    simpa only [card_map] using card_le_card hf
  obtain ⟨U, hU, hUcard⟩ := exists_subset_card_eq hpad
  let u := ∑ i ∈ U, a i
  let g : ℕ ↪ ℕ := ⟨(· + u), fun _ _ h => Nat.add_right_cancel h⟩
  have hg : (sumLayer a T k).map g ⊆ sumLayer a (range n) (n / 2) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
    obtain ⟨V, hV, hVcard, hVsum⟩ := mem_sumLayer.mp hx
    have hdis : Disjoint V U :=
      (disjoint_sdiff : Disjoint T (range n \ T)).mono hV hU
    refine mem_sumLayer.mpr ⟨V ∪ U, union_subset (hV.trans hT) (hU.trans sdiff_subset), ?_, ?_⟩
    · rw [card_union_of_disjoint hdis, hVcard, hUcard]
      omega
    · rw [sum_union hdis, hVsum]
      rfl
  refine hCount.trans ?_
  simpa only [card_map, middleLayer] using card_le_card hg

/-- The opposite pairs in the central portion of a prefix leave enough free indices
to lift their translated carrier to the middle layer. -/
theorem opposite_card_le_middleLayer {a : ℕ → ℕ} {n : ℕ} {P : Finset ℤ} {z : ℤ}
    (hP : ∀ x ∈ P, z + x ∈
      (sumLayer a
        (univ.map (oppositeLow (n / 2) (n / 16)) ∪ univ.map (oppositeHigh (n / 2) (n / 16)))
        (n / 16)).map Nat.castEmbedding) :
    P.card ≤ middleLayer a n := by
  let m := n / 16
  let q := n / 2
  let T := univ.map (oppositeLow q m) ∪ univ.map (oppositeHigh q m)
  have hTc : T.card ≤ 2 * m := by
    dsimp only [T]
    have h := card_union_le (univ.map (oppositeLow q m)) (univ.map (oppositeHigh q m))
    simpa only [card_map, card_univ, Fintype.card_fin, two_mul] using h
  have hT : T ⊆ range n := by
    intro j hj
    rcases mem_union.mp hj with h | h
    · obtain ⟨i, _, rfl⟩ := mem_map.mp h
      apply mem_range.mpr
      change q + (m - 1 - i.val) < n
      have hi := i.isLt
      dsimp [q, m] at *
      omega
    · obtain ⟨i, _, rfl⟩ := mem_map.mp h
      apply mem_range.mpr
      change q + m + i.val < n
      have hi := i.isLt
      dsimp [q, m] at *
      omega
  apply card_le_middleLayer_of_integer_translate (T := T) hT (by omega) _ hP
  rw [card_sdiff_of_subset hT, card_range]
  dsimp [m] at *
  omega

/-- A positive-rank carrier with rank at least `r` directly gives the corresponding
power lower bound without further progression geometry. -/
theorem opposite_rank_direct_middleLayer_bound
    {a : ℕ → ℕ} {n rank r C : ℕ} {P : Finset ℤ} {z : ℤ}
    (hn : 16 ≤ n) (hr : r ≤ rank)
    (hcard : (n / 16) ^ (rank + 1) ≤ C * P.card)
    (hP : ∀ x ∈ P, z + x ∈
      (sumLayer a
        (univ.map (oppositeLow (n / 2) (n / 16)) ∪ univ.map (oppositeHigh (n / 2) (n / 16)))
        (n / 16)).map Nat.castEmbedding) :
    ((n : ℝ) + 1) ^ (r + 1) ≤ ((32 : ℝ) ^ (r + 1) * C) * (middleLayer a n : ℝ) := by
  have hm : 1 ≤ n / 16 := by omega
  have hsmall : n + 1 ≤ 32 * (n / 16) := by omega
  have hmono : (n / 16) ^ (r + 1) ≤ (n / 16) ^ (rank + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hPcount := opposite_card_le_middleLayer hP
  have hx : (((n / 16 : ℕ) : ℝ) ^ (r + 1)) ≤ (C : ℝ) * (middleLayer a n : ℝ) := by
    exact_mod_cast hmono.trans (hcard.trans (Nat.mul_le_mul_left C hPcount))
  calc
    _ ≤ ((32 : ℝ) * ((n / 16 : ℕ) : ℝ)) ^ (r + 1) := by
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast hsmall
    _ = (32 : ℝ) ^ (r + 1) * ((n / 16 : ℕ) : ℝ) ^ (r + 1) := mul_pow _ _ _
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hx (by positivity)

end Jsp000726
