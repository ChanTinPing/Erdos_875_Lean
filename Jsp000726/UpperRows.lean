module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card

import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators

namespace Jsp000726.Upper

/-- Integral cubic and seventh-power row schedules with the rounding performed separately. -/
def rowIndex (N r H i : ℕ) : ℕ :=
  i ^ 3 / N ^ 3 + H * i ^ 7 / r ^ 7

/-- The number of earlier filler indices in the same row. -/
def rowOffset (N r H i : ℕ) : ℕ :=
  ((Finset.range i).filter fun j => rowIndex N r H j = rowIndex N r H i).card

theorem rowIndex_mono (N r H : ℕ) : Monotone (rowIndex N r H) := by
  intro i j hij
  exact Nat.add_le_add (Nat.div_le_div_right (Nat.pow_le_pow_left hij 3))
    (Nat.div_le_div_right (Nat.mul_le_mul_left H (Nat.pow_le_pow_left hij 7)))

theorem rowIndex_end {N r H : ℕ} (hr : 0 < r) :
    rowIndex N r H r = r ^ 3 / N ^ 3 + H := by
  unfold rowIndex
  rw [Nat.mul_comm H, Nat.mul_div_cancel_left H (Nat.pow_pos hr)]

theorem rowIndex_lt_end {N r H i : ℕ} (hr : 0 < r) (hH : 0 < H) (hi : i < r) :
    rowIndex N r H i < rowIndex N r H r := by
  rw [rowIndex_end hr]
  apply Nat.add_lt_add_of_le_of_lt (Nat.div_le_div_right (Nat.pow_le_pow_left hi.le 3))
  apply (Nat.div_lt_iff_lt_mul (Nat.pow_pos hr)).2
  exact Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left hi (by decide)) hH

private theorem cube_sub_lt_of_same_row {N r H i j : ℕ} (hN : 0 < N) (hji : j ≤ i)
    (hrow : rowIndex N r H j = rowIndex N r H i) : i ^ 3 - j ^ 3 < N ^ 3 := by
  have hcm := Nat.div_le_div_right (Nat.pow_le_pow_left hji 3) (c := N ^ 3)
  have hsm := Nat.div_le_div_right (Nat.mul_le_mul_left H (Nat.pow_le_pow_left hji 7))
    (c := r ^ 7)
  have hc : j ^ 3 / N ^ 3 = i ^ 3 / N ^ 3 := by
    unfold rowIndex at hrow
    omega
  have hj := Nat.mul_div_le (j ^ 3) (N ^ 3)
  have hnp : 0 < N ^ 3 := Nat.pow_pos hN
  have hi := Nat.lt_mul_div_succ (i ^ 3) hnp
  rw [← hc, Nat.mul_add, Nat.mul_one] at hi
  omega

private theorem mul_sq_le_cube_sub_of_le {i j : ℕ} (hji : j ≤ i) :
    (i - j) * i ^ 2 ≤ i ^ 3 - j ^ 3 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hji
  rw [Nat.add_sub_cancel_left]
  have heq : (j + k) ^ 3 = j ^ 3 + k * (j + k) ^ 2 + (2 * j * j * k + j * k * k) := by
    ring
  omega

private theorem rowOffset_le_of_distances {N r H i m : ℕ}
    (h : ∀ j < i, rowIndex N r H j = rowIndex N r H i → i - j ≤ m) :
    rowOffset N r H i ≤ m := by
  unfold rowOffset
  rw [← Finset.card_range m]
  apply Finset.card_le_card_of_injOn (fun j => i - j - 1)
  · intro j hmem
    have hj := Finset.mem_filter.mp hmem
    have hlt := Finset.mem_range.mp hj.1
    have hle := h j hlt hj.2
    exact Finset.mem_range.mpr (show i - j - 1 < m by omega)
  · intro j hj k hk heq
    have hj' := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hk' := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    dsimp at heq
    omega

/-- Every row has at most `N` filler indices. -/
theorem rowOffset_lt {N r H i : ℕ} (hN : 0 < N) : rowOffset N r H i < N := by
  suffices rowOffset N r H i ≤ N - 1 by omega
  apply rowOffset_le_of_distances
  intro j hji hrow
  have hmul := mul_sq_le_cube_sub_of_le hji.le
  have hpow : (i - j) ^ 3 ≤ (i - j) * i ^ 2 := by
    rw [pow_succ, mul_comm ((i - j) ^ 2)]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.sub_le i j) 2)
  have hlt := hpow.trans_lt (hmul.trans_lt (cube_sub_lt_of_same_row hN hji.le hrow))
  have hdist : i - j < N := by
    contrapose! hlt
    exact Nat.pow_le_pow_left hlt 3
  omega

/-- Later rows are sparse enough that the total within-row offset is quadratic. -/
theorem rowOffset_le_div {N r H i : ℕ} (hN : 0 < N) (hi : 0 < i) :
    rowOffset N r H i ≤ N ^ 3 / i ^ 2 := by
  apply rowOffset_le_of_distances
  intro j hji hrow
  apply (Nat.le_div_iff_mul_le (Nat.pow_pos hi)).2
  exact (mul_sq_le_cube_sub_of_le hji.le).trans
    (cube_sub_lt_of_same_row hN hji.le hrow).le

@[simp] theorem rowOffset_zero (N r H : ℕ) : rowOffset N r H 0 = 0 := by
  simp [rowOffset]

theorem rowOffset_succ_of_same_row {N r H i : ℕ}
    (h : rowIndex N r H i = rowIndex N r H (i + 1)) :
    rowOffset N r H (i + 1) = rowOffset N r H i + 1 := by
  simp [rowOffset, Finset.range_add_one, Finset.filter_insert, h.symm]

theorem rowOffset_succ_of_row_jump {N r H i : ℕ}
    (h : rowIndex N r H i < rowIndex N r H (i + 1)) :
    rowOffset N r H (i + 1) = 0 := by
  unfold rowOffset
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j hj
  have hj' : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  exact ((rowIndex_mono N r H hj').trans_lt h).ne

/-- The `i`-th filler within a concrete stage. -/
def fillerValue (B g h N r H i : ℕ) : ℕ :=
  B + g * rowIndex N r H i + h * rowOffset N r H i

@[simp] theorem fillerValue_zero (B g h N r H : ℕ) : fillerValue B g h N r H 0 = B := by
  simp [fillerValue, rowIndex]

theorem fillerValue_strictMono {B g h N r H : ℕ}
    (hN : 0 < N) (hh : 0 < h) (hg : h * N ≤ g) :
    StrictMono (fillerValue B g h N r H) := by
  apply strictMono_nat_of_lt_succ
  intro i
  rcases lt_or_eq_of_le (rowIndex_mono N r H (Nat.le_succ i)) with hrow | hrow
  · have ho := Nat.mul_lt_mul_of_pos_left (rowOffset_lt (r := r) (H := H) (i := i) hN) hh
    have hstep := Nat.mul_le_mul_left g (Nat.succ_le_of_lt hrow)
    simp only [Nat.mul_succ, Nat.succ_eq_add_one] at hstep
    unfold fillerValue
    omega
  · have ho := rowOffset_succ_of_same_row hrow
    simp only [fillerValue, ho, Nat.mul_add, Nat.mul_one]
    rw [← hrow]
    omega

theorem fillerValue_gap_le {B g h N r H i : ℕ} :
    fillerValue B g h N r H (i + 1) - fillerValue B g h N r H i ≤
      h + g * (rowIndex N r H (i + 1) - rowIndex N r H i) := by
  rcases lt_or_eq_of_le (rowIndex_mono N r H (Nat.le_succ i)) with hrow | hrow
  · have ho := rowOffset_succ_of_row_jump hrow
    simp only [fillerValue, ho, Nat.mul_zero, Nat.add_zero, Nat.mul_sub_left_distrib]
    have hg := Nat.mul_le_mul_left g hrow.le
    omega
  · have ho := rowOffset_succ_of_same_row hrow
    simp only [fillerValue, ho, Nat.mul_add, Nat.mul_one, ← hrow, Nat.sub_self,
      Nat.mul_zero, Nat.add_zero]
    omega

end Jsp000726.Upper
