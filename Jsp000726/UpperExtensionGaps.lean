module

public import Jsp000726.UpperAssembly
public import Jsp000726.UpperBlock
public import Jsp000726.UpperParametersGap
public import Jsp000726.UpperRowEstimates

@[expose] public section

namespace Jsp000726.Upper

/-- Every gap in the old prefix, filler block, dense block, or a bridge obeys the
all-index cap as soon as the old reference has sufficiently small normalization. -/
theorem extendPrefix_gap_bound {a : List ℕ} {B g h r H R k : ℕ}
    (hN : 0 < a.length) (hr : 0 < r) (hH : 0 < H) (hhg : h ≤ g)
    (hR : r ^ 3 / a.length ^ 3 + H = R - k)
    (hrlo : (a.length : ℝ) ^ sharpS ≤ (r : ℝ))
    (hrhi : (r : ℝ) ≤ 2 * (a.length : ℝ) ^ sharpS)
    (hgH : g * H ≤ B + g * R)
    (hg : (g : ℝ) ≤ 17 * (B : ℝ) * (r : ℝ))
    (hB' : ((B + g * R : ℕ) : ℝ) ≤ 65 * (B : ℝ) * (16900 : ℝ) ^ 2 * (r : ℝ) ^ 4)
    (hsmall : (204 + 455 * (16900 : ℝ) ^ 2) * ((B : ℝ) / (a.length : ℝ) ^ sharpRho) ≤ 1)
    (hold : IndexedGapBound gapThreshold 0 a)
    (hlast : a[a.length - 1]'(by omega) + h = B) :
    IndexedGapBound gapThreshold 0 (extendPrefix a B g h a.length r H R k) := by
  let f := fillerBlock B g h a.length r H
  let D := denseBlock B g R k
  have hlenF : f.length = r := length_fillerBlock _ _ _ _ _ _
  have hlenD : D.length = k := length_denseBlock _ _ _ _
  have hNreal : (1 : ℝ) ≤ (a.length : ℝ) := Nat.one_le_cast.mpr hN
  have hcgh : (g : ℝ) * (H : ℝ) ≤ ((B + g * R : ℕ) : ℝ) := by exact_mod_cast hgH
  have hconstant (n : ℕ) (hn : a.length ≤ n) :
      (g : ℝ) ≤ (n : ℝ) ^ gapThreshold :=
    sharp_dense_gap_cap hNreal (Nat.cast_le.mpr hn) (Nat.cast_nonneg B) hrlo hrhi
      (Nat.cast_nonneg g) (Nat.cast_nonneg _) hg hB' hsmall
  have hrow (i : ℕ) (hi : i + 1 ≤ r) :
      ((fillerValue B g h a.length r H (i + 1) - fillerValue B g h a.length r H i : ℕ) : ℝ) ≤
        ((a.length + i + 1 : ℕ) : ℝ) ^ gapThreshold := by
    have hd := fillerValue_gap_le_real (B := B) (g := g) (h := h) (H := H) (i := i) hN hr
    have hx : (0 : ℝ) ≤ (i : ℝ) + 1 := add_nonneg (Nat.cast_nonneg i) zero_le_one
    have hxr : (i : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast hi
    have hrow := sharp_gap_cap_of_row hNreal hx (Nat.cast_nonneg B) hrlo hrhi hxr
      (Nat.cast_le.mpr hhg) (Nat.cast_nonneg g) (Nat.cast_nonneg H) hcgh hg hB' hsmall
      (by simpa only [mul_assoc] using hd)
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hrow
  have hf : IndexedGapBound gapThreshold a.length f := by
    intro n hn
    rw [getElem_fillerBlock, getElem_fillerBlock]
    exact hrow n (by omega)
  have hd : IndexedGapBound gapThreshold (a.length + f.length) D := by
    intro n hn
    rw [getElem_denseBlock, getElem_denseBlock, denseValue_gap]
    apply hconstant
    omega
  have hfD : IndexedGapBound gapThreshold a.length (f ++ D) := by
    apply indexedGapBound_append hf hd
    intro hf0 hD0
    rw [getElem_denseBlock, getElem_fillerBlock, ← fillerValue_end_eq_dense_zero (h := h) hr hH hR]
    have hr' : f.length - 1 + 1 = r := by omega
    have hh := hrow (f.length - 1) hr'.le
    have hi : a.length + (f.length - 1) + 1 = a.length + f.length := by omega
    rw [hr', hi] at hh
    exact hh
  have hall : IndexedGapBound gapThreshold 0 (a ++ (f ++ D)) := by
    apply indexedGapBound_append hold (by simpa only [zero_add] using hfD)
    intro ha0 hnew
    rw [List.getElem_append_left (show 0 < f.length by omega), getElem_fillerBlock,
      fillerValue_zero, zero_add]
    have he : B - a[a.length - 1] = h := by omega
    rw [he]
    exact (Nat.cast_le.mpr hhg).trans (hconstant a.length le_rfl)
  simpa only [extendPrefix, List.append_assoc, f, D] using hall

end Jsp000726.Upper
