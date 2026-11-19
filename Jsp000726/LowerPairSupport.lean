module

public import Jsp000726.LowerPairing
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace Jsp000726

open Finset

def oppositeSupport (q m : ℕ) : Finset ℕ :=
  univ.map (oppositeLow q m) ∪ univ.map (oppositeHigh q m)

/-- The opposite pairs partition their index interval. -/
theorem oppositeSupport_eq_Ico (q m : ℕ) : oppositeSupport q m = Finset.Ico q (q + 2 * m) := by
  ext x
  constructor
  · intro hx
    rcases mem_union.mp hx with hl | hr
    · obtain ⟨i, _, hi⟩ := mem_map.mp hl
      rw [← hi]
      apply mem_Ico.mpr
      have h := i.isLt
      change q ≤ q + (m - 1 - i.val) ∧ q + (m - 1 - i.val) < q + 2 * m
      omega
    · obtain ⟨i, _, hi⟩ := mem_map.mp hr
      rw [← hi]
      apply mem_Ico.mpr
      have h := i.isLt
      change q ≤ q + m + i.val ∧ q + m + i.val < q + 2 * m
      omega
  · intro hx
    obtain ⟨ha, hb⟩ := mem_Ico.mp hx
    apply mem_union.mpr
    by_cases h : x < q + m
    · let i : Fin m := ⟨q + m - 1 - x, by omega⟩
      refine Or.inl (mem_map.mpr ⟨i, mem_univ _, ?_⟩)
      change q + (m - 1 - (q + m - 1 - x)) = x
      omega
    · let i : Fin m := ⟨x - (q + m), by omega⟩
      refine Or.inr (mem_map.mpr ⟨i, mem_univ _, ?_⟩)
      change q + m + (x - (q + m)) = x
      omega

theorem oppositeSupport_card (q m : ℕ) : (oppositeSupport q m).card = 2 * m := by
  rw [oppositeSupport_eq_Ico, Nat.card_Ico]
  omega

theorem oppositeSupport_subset_range {q m n : ℕ} (h : q + 2 * m ≤ n) :
    oppositeSupport q m ⊆ range n := by
  intro i hi
  rw [oppositeSupport_eq_Ico] at hi
  exact mem_range.mpr ((mem_Ico.mp hi).2.trans_le h)

theorem disjoint_range_oppositeSupport {q m r : ℕ} (h : r ≤ q) :
    Disjoint (range r) (oppositeSupport q m) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  rw [oppositeSupport_eq_Ico] at hj
  have hi' := mem_range.mp hi
  have hj' := (mem_Ico.mp hj).1
  omega

end Jsp000726
