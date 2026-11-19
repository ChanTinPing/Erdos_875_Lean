module

public import Jsp000726.UpperRows
public import Mathlib.Data.List.Basic

@[expose] public section

namespace Jsp000726.Upper

/-- The filler portion of a stage, in increasing order. -/
def fillerBlock (B g h N r H : ℕ) : List ℕ :=
  (List.range r).map (fillerValue B g h N r H)

/-- The `j`-th dense term. The last dense term is one step below the new reference. -/
def denseValue (B g R k j : ℕ) : ℕ :=
  B + g * (R - k + j)

/-- The final arithmetic progression of a stage, in increasing order. -/
def denseBlock (B g R k : ℕ) : List ℕ :=
  (List.range k).map (denseValue B g R k)

/-- Concatenate the old terms, new fillers, and dense terms. -/
def extendPrefix (a : List ℕ) (B g h N r H R k : ℕ) : List ℕ :=
  (a ++ fillerBlock B g h N r H) ++ denseBlock B g R k

@[simp] theorem length_fillerBlock (B g h N r H : ℕ) :
    (fillerBlock B g h N r H).length = r := by simp [fillerBlock]

@[simp] theorem length_denseBlock (B g R k : ℕ) :
    (denseBlock B g R k).length = k := by simp [denseBlock]

@[simp] theorem length_extendPrefix (a : List ℕ) (B g h N r H R k : ℕ) :
    (extendPrefix a B g h N r H R k).length = a.length + r + k := by
  simp [extendPrefix, Nat.add_assoc]

@[simp] theorem getElem_fillerBlock {B g h N r H i : ℕ}
    (hi : i < (fillerBlock B g h N r H).length) :
    (fillerBlock B g h N r H)[i] = fillerValue B g h N r H i := by
  simp [fillerBlock]

@[simp] theorem getElem_denseBlock {B g R k i : ℕ}
    (hi : i < (denseBlock B g R k).length) :
    (denseBlock B g R k)[i] = denseValue B g R k i := by
  simp [denseBlock]

theorem denseValue_strictMono {B g R k : ℕ} (hg : 0 < g) :
    StrictMono (denseValue B g R k) := by
  intro i j hij
  exact Nat.add_lt_add_left
    (Nat.mul_lt_mul_of_pos_left (Nat.add_lt_add_left hij (R - k)) hg) B

@[simp] theorem denseValue_gap (B g R k j : ℕ) :
    denseValue B g R k (j + 1) - denseValue B g R k j = g := by
  simp only [denseValue, Nat.mul_add, Nat.mul_one]
  omega

theorem fillerValue_end_eq_dense_zero {B g h N r H R k : ℕ}
    (hr : 0 < r) (hH : 0 < H) (hR : r ^ 3 / N ^ 3 + H = R - k) :
    fillerValue B g h N r H r = denseValue B g R k 0 := by
  have hz : rowOffset N r H r = 0 := by
    unfold rowOffset
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i hi
    exact (rowIndex_lt_end hr hH (Finset.mem_range.mp hi)).ne
  simp only [fillerValue, denseValue, hz, Nat.mul_zero, Nat.add_zero,
    rowIndex_end hr, hR]

theorem fillerValue_lt_dense_zero {B g h N r H R k i : ℕ}
    (hN : 0 < N) (hh : 0 < h) (hgn : h * N ≤ g)
    (hH : 0 < H) (hR : r ^ 3 / N ^ 3 + H = R - k) (hi : i < r) :
    fillerValue B g h N r H i < denseValue B g R k 0 := by
  rw [← fillerValue_end_eq_dense_zero (Nat.zero_lt_of_lt hi) hH hR]
  exact fillerValue_strictMono hN hh hgn hi

theorem denseValue_le_reference_sub_step {B g R k j : ℕ} (hk : k ≤ R) (hj : j < k) :
    denseValue B g R k j + g ≤ B + g * R := by
  have hl : R - k + j + 1 ≤ R := by omega
  unfold denseValue
  have hm := Nat.mul_le_mul_left g hl
  simp only [Nat.mul_add, Nat.mul_one] at hm ⊢
  omega

theorem denseValue_last_add_step {B g R k : ℕ} (hk : k ≤ R) (hk0 : 0 < k) :
    denseValue B g R k (k - 1) + g = B + g * R := by
  unfold denseValue
  have hl : R - k + (k - 1) + 1 = R := by omega
  calc
    B + g * (R - k + (k - 1)) + g = B + g * (R - k + (k - 1) + 1) := by
      simp only [Nat.mul_add, Nat.mul_one]
      omega
    _ = _ := by rw [hl]

theorem extendPrefix_pairwise {a : List ℕ} {B g h N r H R k : ℕ}
    (ha : a.Pairwise (· < ·)) (haB : ∀ x ∈ a, x < B)
    (hN : 0 < N) (hh : 0 < h) (hg : 0 < g) (hgn : h * N ≤ g)
    (hH : 0 < H) (hR : r ^ 3 / N ^ 3 + H = R - k) :
    (extendPrefix a B g h N r H R k).Pairwise (· < ·) := by
  have hf : (fillerBlock B g h N r H).Pairwise (· < ·) := by
    unfold fillerBlock
    exact List.pairwise_map.mpr (List.pairwise_lt_range.imp
      (fun hij => fillerValue_strictMono hN hh hgn hij))
  have hd : (denseBlock B g R k).Pairwise (· < ·) := by
    unfold denseBlock
    exact List.pairwise_map.mpr (List.pairwise_lt_range.imp
      (fun hij => denseValue_strictMono hg hij))
  apply List.pairwise_append.mpr
  refine ⟨List.pairwise_append.mpr ⟨ha, hf, ?_⟩, hd, ?_⟩
  · intro x hx y hy
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hy
    exact (haB x hx).trans_le (by unfold fillerValue; omega)
  · intro x hx y hy
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy
    rcases List.mem_append.mp hx with ha' | hf'
    · exact (haB x ha').trans_le (by unfold denseValue; omega)
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf'
    exact (fillerValue_lt_dense_zero hN hh hgn hH hR (List.mem_range.mp hi)).trans_le
      ((denseValue_strictMono hg).monotone (Nat.zero_le j))

theorem extendPrefix_le_reference_sub_step {a : List ℕ} {B g h N r H R k x : ℕ}
    (haB : ∀ x ∈ a, x < B) (hN : 0 < N) (hh : 0 < h) (hgn : h * N ≤ g)
    (hH : 0 < H) (hR : r ^ 3 / N ^ 3 + H = R - k)
    (hk : k ≤ R) (hk0 : 0 < k) (hx : x ∈ extendPrefix a B g h N r H R k) :
    x + g ≤ B + g * R := by
  rcases List.mem_append.mp hx with hx | hx
  · have hd := denseValue_le_reference_sub_step (B := B) (g := g) hk hk0
    apply Nat.le_trans _ hd
    apply Nat.add_le_add_right
    rcases List.mem_append.mp hx with ha' | hf'
    · exact (haB x ha').le.trans (by unfold denseValue; omega)
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf'
    exact (fillerValue_lt_dense_zero hN hh hgn hH hR (List.mem_range.mp hi)).le
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    exact denseValue_le_reference_sub_step hk (List.mem_range.mp hj)

theorem extendPrefix_positive {a : List ℕ} {B g h N r H R k x : ℕ}
    (ha : ∀ x ∈ a, 0 < x) (hB : 0 < B) (hx : x ∈ extendPrefix a B g h N r H R k) :
    0 < x := by
  rcases List.mem_append.mp hx with hx | hx
  · rcases List.mem_append.mp hx with hx | hx
    · exact ha x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    unfold fillerValue
    omega
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    unfold denseValue
    omega

theorem extendPrefix_last_add_step {a : List ℕ} {B g h N r H R k : ℕ}
    (hk : k ≤ R) (hk0 : 0 < k) :
    (extendPrefix a B g h N r H R k)[(extendPrefix a B g h N r H R k).length - 1]'
      (by simp; omega) + g = B + g * R := by
  let D := denseBlock B g R k
  let b := extendPrefix a B g h N r H R k
  have hd : D.getLast? = some (denseValue B g R k (k - 1)) := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by simp [D]; omega)]
    simp [D]
  have hget : b.getLast? = some (denseValue B g R k (k - 1)) := by
    change (((a ++ fillerBlock B g h N r H) ++ D).getLast?) = _
    simp [hd]
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by simp [b]; omega)] at hget
  change b[b.length - 1]'(by simp [b]; omega) + g = B + g * R
  rw [Option.some.inj hget]
  exact denseValue_last_add_step hk hk0

end Jsp000726.Upper
