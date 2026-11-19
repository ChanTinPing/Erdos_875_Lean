module

public import Jsp000726.UpperConcrete
public import Jsp000726.UpperAssembly

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

@[expose] public section

namespace Jsp000726.Upper

/-- The initial interval ends one below this reference. -/
def seedReference (N : ℕ) : ℕ := 12 * N ^ 2 + N

/-- Start from a consecutive interval with count N and step one. -/
def seedPrefix (N : ℕ) : List ℕ :=
  (List.range N).map (fun i => 12 * N ^ 2 + i)

@[simp] theorem length_seedPrefix (N : ℕ) : (seedPrefix N).length = N := by
  simp [seedPrefix]

@[simp] theorem getElem_seedPrefix {N i : ℕ} (hi : i < (seedPrefix N).length) :
    (seedPrefix N)[i] = 12 * N ^ 2 + i := by
  simp [seedPrefix]

theorem seedPrefix_pairwise (N : ℕ) : (seedPrefix N).Pairwise (· < ·) := by
  unfold seedPrefix
  exact List.pairwise_map.mpr (List.pairwise_lt_range.imp
    (fun hij => Nat.add_lt_add_left hij (12 * N ^ 2)))

theorem seedPrefix_lt_reference {N x : ℕ} (hx : x ∈ seedPrefix N) :
    x < seedReference N := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact Nat.add_lt_add_left (List.mem_range.mp hi) _

theorem seedPrefix_positive {N x : ℕ} (hN : 0 < N) (hx : x ∈ seedPrefix N) : 0 < x := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  exact (Nat.mul_pos (by decide) (Nat.pow_pos hN)).trans_le (Nat.le_add_right _ _)

theorem seedPrefix_last_add_one {N : ℕ} (hN : 0 < N) :
    (seedPrefix N)[N - 1]'(by simp; omega) + 1 = seedReference N := by
  simp only [getElem_seedPrefix, seedReference]
  omega

theorem seedPrefix_gap_eq_one {N i : ℕ} (hi : i + 1 < (seedPrefix N).length) :
    (seedPrefix N)[i + 1] - (seedPrefix N)[i]'(by omega) = 1 := by
  simp only [getElem_seedPrefix]
  omega

theorem seedPrefix_gap_bound (N : ℕ) : IndexedGapBound gapThreshold 0 (seedPrefix N) := by
  intro i hi
  rw [seedPrefix_gap_eq_one hi, Nat.cast_one]
  have hone : 1 ≤ ((0 + i + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 0 + i + 1 by omega)
  exact Real.one_le_rpow hone (by unfold gapThreshold; positivity)

theorem seedPrefix_invariant (N : ℕ) :
    invariant (integerTerms (seedPrefix N)) (seedReference N) 1 1 := by
  intro weight hw q hdiv
  exact one_dvd _

theorem seedPrefix_budget {N : ℕ} (hN : 0 < N) :
    mass (integerTerms (seedPrefix N)) (seedReference N) +
      10 * (N : ℤ) ^ 2 < (seedReference N : ℤ) := by
  let A := integerTerms (seedPrefix N)
  have hdist x (hx : x ∈ A) : |x - (seedReference N : ℤ)| ≤ N := by
    obtain ⟨y, hy, rfl⟩ := mem_integerTerms.mp hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
    have hi' : (i : ℤ) < N := by exact_mod_cast List.mem_range.mp hi
    apply abs_le.mpr
    simp only [seedReference, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    have hi0 := Int.natCast_nonneg i
    omega
  have hcard : A.card ≤ N := by
    simpa [A] using integerTerms_card_le (seedPrefix N)
  have hmass : mass A (seedReference N) ≤ (N : ℤ) * N :=
    (mass_le_card_mul hdist).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Int.natCast_nonneg N))
  have hNi : 0 < (N : ℤ) := by exact_mod_cast hN
  simp only [seedReference, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hmass ⊢
  nlinarith only [hmass, hNi, sq_nonneg (N : ℤ)]

end Jsp000726.Upper
