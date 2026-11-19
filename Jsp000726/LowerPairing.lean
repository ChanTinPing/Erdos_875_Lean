module

public import Jsp000726.LowerLayers

@[expose] public section

namespace Jsp000726

open Finset

/-- Switching from the low to the high endpoint in any selection of disjoint pairs preserves
cardinality and adds exactly the sum of the corresponding differences. -/
theorem mem_sumLayer_of_pair_selection {a : ℕ → ℕ} {m : ℕ}
    (lo hi : Fin m ↪ ℕ) (hle : ∀ i, a (lo i) ≤ a (hi i))
    (hdis : Disjoint (univ.map lo) (univ.map hi)) (S : Finset (Fin m)) :
    ((∑ i : Fin m, a (lo i)) + ∑ i ∈ S, (a (hi i) - a (lo i))) ∈
      sumLayer a (univ.map lo ∪ univ.map hi) m := by
  let L := (univ \ S).map lo
  let R := S.map hi
  have hL : L ⊆ univ.map lo := by
    intro j hj
    obtain ⟨i, _, rfl⟩ := mem_map.mp hj
    exact mem_map.mpr ⟨i, mem_univ i, rfl⟩
  have hR : R ⊆ univ.map hi := by
    intro j hj
    obtain ⟨i, _, rfl⟩ := mem_map.mp hj
    exact mem_map.mpr ⟨i, mem_univ i, rfl⟩
  refine mem_sumLayer.mpr ⟨L ∪ R, union_subset_union hL hR, ?_, ?_⟩
  · rw [card_union_of_disjoint (hdis.mono hL hR)]
    simp only [L, R, card_map, card_sdiff_of_subset (subset_univ S), card_univ, Fintype.card_fin]
    exact Nat.sub_add_cancel (by simpa using card_le_card (subset_univ S))
  · rw [sum_union (hdis.mono hL hR)]
    simp only [L, R, sum_map]
    have hpart : (∑ i ∈ univ \ S, a (lo i)) + (∑ i ∈ S, a (lo i)) = ∑ i, a (lo i) :=
      sum_sdiff (subset_univ S)
    have hdiff : (∑ i ∈ S, a (lo i)) + (∑ i ∈ S, (a (hi i) - a (lo i))) =
        ∑ i ∈ S, a (hi i) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun i _ => Nat.add_sub_of_le (hle i)
    omega

/-- The lower endpoints of opposite pairs in the interval `[q,q+2m)`. -/
def oppositeLow (q m : ℕ) : Fin m ↪ ℕ where
  toFun i := q + (m - 1 - i.val)
  inj' i j h := by
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    dsimp at h
    omega

/-- The upper endpoints of opposite pairs in the interval `[q,q+2m)`. -/
def oppositeHigh (q m : ℕ) : Fin m ↪ ℕ where
  toFun i := q + m + i.val
  inj' i j h := by
    apply Fin.ext
    dsimp at h
    omega

private theorem opposite_low_lt_high {q m : ℕ} (i j : Fin m) :
    oppositeLow q m i < oppositeHigh q m j := by
  have hi := i.isLt
  change q + (m - 1 - i.val) < q + m + j.val
  omega

private theorem opposite_disjoint (q m : ℕ) :
    Disjoint (univ.map (oppositeLow q m)) (univ.map (oppositeHigh q m)) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, _, hi⟩ := mem_map.mp hx
  obtain ⟨j, _, hj⟩ := mem_map.mp hy
  exact (opposite_low_lt_high i j).ne (hi.trans hj.symm)

/-- Opposite-pair differences, in increasing order from the innermost to outermost pair. -/
def oppositeDifference (a : ℕ → ℕ) (q m : ℕ) (i : Fin m) : ℕ :=
  a (oppositeHigh q m i) - a (oppositeLow q m i)

theorem oppositeDifference_pos {a : ℕ → ℕ} (ha : StrictMono a) (q m : ℕ) (i : Fin m) :
    0 < oppositeDifference a q m i :=
  Nat.sub_pos_of_lt (ha (opposite_low_lt_high i i))

theorem strictMono_oppositeDifference {a : ℕ → ℕ} (ha : StrictMono a) (q m : ℕ) :
    StrictMono (oppositeDifference a q m) := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  have hvals : i.val < j.val := hij
  have hlow : oppositeLow q m j < oppositeLow q m i := by
    change q + (m - 1 - j.val) < q + (m - 1 - i.val)
    omega
  have hhigh : oppositeHigh q m i < oppositeHigh q m j := by
    change q + m + i.val < q + m + j.val
    omega
  have hs := ha (opposite_low_lt_high (q := q) i i)
  have hlo := ha hlow
  have hhi := ha hhigh
  unfold oppositeDifference
  omega

/-- Each unrestricted subset sum of opposite differences lifts into one cardinality layer. -/
theorem mem_sumLayer_of_opposite_selection {a : ℕ → ℕ} (ha : StrictMono a) (q m : ℕ)
    (S : Finset (Fin m)) :
    ((∑ i : Fin m, a (oppositeLow q m i)) + ∑ i ∈ S, oppositeDifference a q m i) ∈
      sumLayer a (univ.map (oppositeLow q m) ∪ univ.map (oppositeHigh q m)) m :=
  mem_sumLayer_of_pair_selection (oppositeLow q m) (oppositeHigh q m)
    (fun i => (ha (opposite_low_lt_high i i)).le) (opposite_disjoint q m) S

end Jsp000726
