module

public import Jsp000726.DyadicSixth
public import Jsp000726.LowerPairing
public import Jsp000726.LowerDensity
public import Jsp000726.LowerGrowth
public import Mathlib.Data.Finset.Preimage

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

namespace Jsp000726

open Filter Finset PublicStructure

/-- Strictly ordered opposite-pair differences, viewed as a finite set of integers. -/
def oppositeDifferenceEmbedding {a : ℕ → ℕ} (ha : StrictMono a) (q m : ℕ) : Fin m ↪ ℤ :=
  (⟨oppositeDifference a q m, (strictMono_oppositeDifference ha q m).injective⟩ :
    Fin m ↪ ℕ).trans Nat.castEmbedding

theorem oppositeDifferenceSet_subset {a : ℕ → ℕ} (ha : StrictMono a)
    (q m N : ℕ) (hN : a (q + 2 * m) ≤ N) :
    univ.map (oppositeDifferenceEmbedding ha q m) ⊆ Icc 1 (N : ℤ) := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := mem_map.mp hx
  have hlo := oppositeDifference_pos ha q m i
  have hhi : oppositeDifference a q m i ≤ N := by
    apply (Nat.sub_le _ _).trans _
    apply (ha.monotone ?_).trans hN
    change q + m + i.val ≤ q + 2 * m
    have hi := i.isLt
    omega
  apply mem_Icc.mpr
  change 1 ≤ (oppositeDifference a q m i : ℤ) ∧ (oppositeDifference a q m i : ℤ) ≤ N
  exact ⟨by exact_mod_cast (Nat.one_le_of_lt hlo), by exact_mod_cast hhi⟩

/-- A sum of arbitrary opposite-pair differences translates to the fixed-size
subset-sum layer formed by choosing one endpoint from each pair. -/
theorem oppositeDifference_sum_translate {a : ℕ → ℕ} (ha : StrictMono a) (q m : ℕ)
    {x : ℤ} (hx : x ∈ (univ.map (oppositeDifferenceEmbedding ha q m)).subsetSum) :
    ((∑ i : Fin m, a (oppositeLow q m i) : ℕ) : ℤ) + x ∈
      (sumLayer a (univ.map (oppositeLow q m) ∪ univ.map (oppositeHigh q m)) m).map
        Nat.castEmbedding := by
  obtain ⟨T, hT, hsum⟩ := mem_subsetSum_iff.mp hx
  let e := oppositeDifferenceEmbedding ha q m
  let U := T.preimage e e.injective.injOn
  have hU : U.map e = T := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, hi, rfl⟩ := mem_map.mp hy
      exact mem_preimage.mp hi
    · intro hy
      obtain ⟨i, _, hi⟩ := mem_map.mp (hT hy)
      exact mem_map.mpr ⟨i, mem_preimage.mpr (hi.symm ▸ hy), hi⟩
  have he (i : Fin m) : e i = (oppositeDifference a q m i : ℤ) := rfl
  have hs : (∑ i ∈ U, (oppositeDifference a q m i : ℤ)) = x := by
    simpa only [← hU, sum_map, he] using hsum
  refine mem_map.mpr ⟨_, mem_sumLayer_of_opposite_selection ha q m U, ?_⟩
  change ((∑ i : Fin m, a (oppositeLow q m i)) + ∑ i ∈ U, oppositeDifference a q m i : ℕ) =
    (((∑ i : Fin m, a (oppositeLow q m i)) : ℕ) : ℤ) + x
  simp only [Nat.cast_add, Nat.cast_sum, hs]

/-- The structural input supplies the precise progression size and rank in the
fixed-cardinality layer of opposite pairs. -/
theorem opposite_layer_structure (h : PowerSubsetStructure) :
    ∃ D C : ℕ, 0 < D ∧ 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ (a : ℕ → ℕ) (_ : StrictMono a) (q m : ℕ),
        a (q + 2 * m) ≤ N → N ≤ m ^ 6 →
        ∃ P : IntegerGAP, 0 < P.rank ∧ P.rank ≤ D ∧ P.Proper ∧
          (∀ i, m ≤ C * P.length i) ∧ m ^ (P.rank + 1) ≤ C * P.carrier.card ∧
          ∀ x ∈ P.carrier, ((∑ i : Fin m, a (oppositeLow q m i) : ℕ) : ℤ) + x ∈
            (sumLayer a (univ.map (oppositeLow q m) ∪ univ.map (oppositeHigh q m)) m).map
              Nat.castEmbedding := by
  obtain ⟨D, C, hD, hC, hstruct⟩ := h
  refine ⟨D, C, hD, hC, hstruct.mono ?_⟩
  intro N hN a ha q m haN hNm
  obtain ⟨P, hP0, hPD, hProper, hsub, hlength, hcard⟩ :=
    hN _ (oppositeDifferenceSet_subset ha q m N haN) (by simpa using hNm)
  refine ⟨P, hP0, hPD, hProper, ?_, ?_, ?_⟩
  · simpa using hlength
  · simpa using hcard
  · intro x hx
    exact oppositeDifference_sum_translate ha q m (hsub hx)

/-- For a polynomially bounded input with exponent below six, the opposite pairs
used in Section 4 admit the structural witnesses at all sufficiently large indices. -/
theorem eventually_opposite_layer_structure {a : ℕ → ℕ} (ha : StrictMono a)
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₆ : p < 6) (haPoly : PolynomialTermBound a p)
    (hstruct : PowerSubsetStructure) :
    ∃ D C : ℕ, 0 < D ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        let q := n / 2
        let m := n / 16
        ∃ P : IntegerGAP, 0 < P.rank ∧ P.rank ≤ D ∧ P.Proper ∧
          (∀ i, m ≤ C * P.length i) ∧ m ^ (P.rank + 1) ≤ C * P.carrier.card ∧
          ∀ x ∈ P.carrier, ((∑ i : Fin m, a (oppositeLow q m i) : ℕ) : ℤ) + x ∈
            (sumLayer a (univ.map (oppositeLow q m) ∪ univ.map (oppositeHigh q m)) m).map
              Nat.castEmbedding := by
  obtain ⟨B, hB, hPoly⟩ := haPoly
  obtain ⟨D, C, hD, hC, h⟩ := opposite_layer_structure hstruct
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  have hsize : ∀ᶠ n : ℕ in atTop, (1 / 64 : ℝ) * (n : ℝ) ≤ ((n / 16 : ℕ) : ℝ) := by
    refine eventually_atTop.mpr ⟨32, fun n hn => ?_⟩
    have hb : n ≤ 64 * (n / 16) := by omega
    have hreal : (n : ℝ) ≤ 64 * ((n / 16 : ℕ) : ℝ) := by exact_mod_cast hb
    linarith
  have hambient : ∀ᶠ n : ℕ in atTop, (a n : ℝ) ≤ (B * (2 : ℝ) ^ p) * (n : ℝ) ^ p := by
    refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    have hn' : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
    calc
      (a n : ℝ) ≤ B * ((n + 1 : ℕ) : ℝ) ^ p := hPoly n
      _ ≤ B * (2 * (n : ℝ)) ^ p := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by push_cast; linarith) hp₀) hB.le
      _ = _ := by rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg _), mul_assoc]
  have hbound := eventually_ambient_le_card_sixth (p := p) hp₆ (by norm_num) hambient hsize
  have hmono_lower (n : ℕ) : n ≤ a n := by
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => exact Nat.succ_le_of_lt (ih.trans_lt (ha (Nat.lt_succ_self _)))
  refine ⟨D, C, hD, hC, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop N] with n hsize hn
  have hidx : n / 2 + 2 * (n / 16) ≤ n := by omega
  exact hN (a n) (hn.trans (hmono_lower n)) a ha (n / 2) (n / 16) (ha.monotone hidx) hsize

end Jsp000726
