module

public import Jsp000726.UpperInvariant
public import Mathlib.Data.Finset.Card

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators

namespace Jsp000726.Upper

theorem mass_nonneg (A : Finset ℤ) (B : ℤ) : 0 ≤ mass A B :=
  Finset.sum_nonneg fun x _ => abs_nonneg (x - B)

theorem mass_union {A C : Finset ℤ} (hAC : Disjoint A C) (B : ℤ) :
    mass (A ∪ C) B = mass A B + mass C B := Finset.sum_union hAC

theorem mass_le_card_mul {A : Finset ℤ} {B M : ℤ}
    (h : ∀ x ∈ A, |x - B| ≤ M) : mass A B ≤ (A.card : ℤ) * M := by
  calc
    _ ≤ ∑ _x ∈ A, M := Finset.sum_le_sum h
    _ = _ := by simp

/-- A dense tail and the earlier fillers fit inside the next deviation budget. -/
theorem next_mass_budget {A C D : Finset ℤ} {N r k B' g K : ℕ}
    (hA : A.card ≤ N) (hC : C.card ≤ r) (hD : D.card ≤ k)
    (hdisj : Disjoint (A ∪ C) D)
    (hACdist : ∀ x ∈ A ∪ C, |x - (B' : ℤ)| ≤ B')
    (hDdist : ∀ x ∈ D, |x - (B' : ℤ)| ≤ (g : ℤ) * k)
    (hK : 8 * (N + r) ≤ K) (hk : N + r ≤ k)
    (hcap : 64 * g * k ^ 2 ≤ B' * K) (hpos : 0 < B' * K) :
    mass ((A ∪ C) ∪ D) B' + 10 * (g : ℤ) * (N + r + k : ℤ) ^ 2 < (B' : ℤ) * K := by
  have hcardAC : (A ∪ C).card ≤ N + r :=
    (Finset.card_union_le A C).trans (Nat.add_le_add hA hC)
  have hmassAC : mass (A ∪ C) B' ≤ (N + r : ℤ) * B' :=
    (mass_le_card_mul hACdist).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hcardAC) (Int.natCast_nonneg B'))
  have hmassD : mass D B' ≤ (g : ℤ) * (k : ℤ) ^ 2 := by
    refine (mass_le_card_mul hDdist).trans ?_
    calc
      _ ≤ (k : ℤ) * ((g : ℤ) * k) := mul_le_mul_of_nonneg_right (by exact_mod_cast hD)
        (mul_nonneg (Int.natCast_nonneg g) (Int.natCast_nonneg k))
      _ = _ := by ring
  have hmassAC8 : 8 * mass (A ∪ C) B' ≤ (B' : ℤ) * K := by
    calc
      _ ≤ 8 * ((N + r : ℤ) * B') := mul_le_mul_of_nonneg_left hmassAC (by decide)
      _ = (B' : ℤ) * (8 * (N + r)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast hK) (Int.natCast_nonneg B')
  have hsize : (N + r + k : ℤ) ≤ 2 * (k : ℤ) := by
    have hki : (N + r : ℤ) ≤ k := by exact_mod_cast hk
    omega
  have hsize2 : (N + r + k : ℤ) ^ 2 ≤ (2 * (k : ℤ)) ^ 2 :=
    pow_le_pow_left₀ (add_nonneg (add_nonneg (Int.natCast_nonneg N) (Int.natCast_nonneg r))
      (Int.natCast_nonneg k)) hsize 2
  have hsize40 : 10 * (g : ℤ) * (N + r + k : ℤ) ^ 2 ≤ 40 * (g : ℤ) * (k : ℤ) ^ 2 := by
    calc
      _ ≤ 10 * (g : ℤ) * (2 * (k : ℤ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsize2 (mul_nonneg (by decide) (Int.natCast_nonneg g))
      _ = _ := by ring
  have hcap' : 64 * (g : ℤ) * (k : ℤ) ^ 2 ≤ (B' : ℤ) * K := by exact_mod_cast hcap
  have hpos' : 0 < (B' : ℤ) * K := by exact_mod_cast hpos
  rw [mass_union hdisj]
  nlinarith only [hmassAC8, hmassD, hsize40, hcap', hpos']

/-- The old budget bounds each prospective filler gap below the new modulus. -/
theorem old_step_mul_le_new_step {A : Finset ℤ} {N B h d K : ℕ}
    (hN : 0 < N) (hdK : d ≤ K)
    (hbudget : mass A B + 10 * (h : ℤ) * (N : ℤ) ^ 2 < (B : ℤ) * d) :
    h * N ≤ B * K := by
  have hsq : N ≤ N ^ 2 := by
    rw [pow_two]
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left N hN
  have hmul := Nat.mul_le_mul_left h hsq
  have hmul' : (h : ℤ) * N ≤ (h : ℤ) * (N : ℤ) ^ 2 := by exact_mod_cast hmul
  have hm := mass_nonneg A B
  have hhr := mul_nonneg (Int.natCast_nonneg h) (sq_nonneg (N : ℤ))
  have hle : (h : ℤ) * N ≤ (B : ℤ) * d := by nlinarith only [hmul', hm, hhr, hbudget]
  exact (show h * N ≤ B * d by exact_mod_cast hle).trans (Nat.mul_le_mul_left B hdK)

end Jsp000726.Upper
