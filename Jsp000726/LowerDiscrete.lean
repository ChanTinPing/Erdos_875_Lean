module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Range
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Data.Nat.Find

@[expose] public section

namespace Jsp000726

open Finset

/-- A walk on a finite set of integers with bounded jumps cannot travel farther than the
jump bound times the number of available values. -/
theorem integer_walk_le {f : ℕ → ℤ} {s : Finset ℤ} (hs : ∀ n, f n ∈ s)
    {D : ℕ} (hstep : ∀ n, f (n + 1) ≤ f n + D) (n : ℕ) :
    f n ≤ f 0 + ((D : ℤ) + 1) * s.card := by
  classical
  by_contra! hn
  let threshold (j : ℕ) := f 0 + ((D : ℤ) + 1) * j
  have hfactor : 0 ≤ (D : ℤ) + 1 := by omega
  have hmono : Monotone threshold := by
    intro j k hjk
    dsimp [threshold]
    have hmul := mul_le_mul_of_nonneg_left (Int.ofNat_le.mpr hjk) hfactor
    omega
  have hreach {j : ℕ} (hj : j ≤ s.card) : ∃ t, threshold j ≤ f t :=
    ⟨n, (hmono hj).trans (le_of_lt hn)⟩
  let hit (j : ℕ) := if h : ∃ t, threshold j ≤ f t then f (Nat.find h) else 0
  have hhit {j : ℕ} (hj : j ≤ s.card) :
      hit j ∈ s ∧ threshold j ≤ hit j ∧ hit j < threshold j + ((D : ℤ) + 1) := by
    have h := hreach hj
    have hlo : threshold j ≤ f (Nat.find h) := Nat.find_spec h
    have hhi : f (Nat.find h) < threshold j + ((D : ℤ) + 1) := by
      by_cases hz : Nat.find h = 0
      · rw [hz]
        have hf : f 0 ≤ threshold j := by
          have h := hmono (Nat.zero_le j)
          simpa only [threshold, Nat.cast_zero, mul_zero, add_zero] using h
        omega
      · have hlt : Nat.find h - 1 < Nat.find h := by omega
        have hprev := Nat.find_min h hlt
        have hstep' := hstep (Nat.find h - 1)
        have heq : Nat.find h - 1 + 1 = Nat.find h := by omega
        rw [heq] at hstep'
        omega
    simpa only [hit, dite_eq_left h] using And.intro (hs (Nat.find h)) (And.intro hlo hhi)
  have hinj : (range (s.card + 1) : Set ℕ).InjOn hit := by
    have hsep {i j : ℕ} (hi : i ≤ s.card) (hj : j ≤ s.card) (hij : i < j) : hit i < hit j := by
      have hsuc : threshold i + ((D : ℤ) + 1) = threshold (i + 1) := by
        dsimp [threshold]
        rw [mul_add, mul_one, add_assoc]
      have h := (hhit hi).2.2.trans_le ((hsuc.le).trans (hmono (Nat.succ_le_of_lt hij)))
      exact h.trans_le (hhit hj).2.1
    intro i hi j hj heq
    have hi' : i ≤ s.card := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hj' : j ≤ s.card := Nat.lt_succ_iff.mp (mem_range.mp hj)
    rcases lt_trichotomy i j with h | h | h
    · exact False.elim ((hsep hi' hj' h).ne heq)
    · exact h
    · exact False.elim ((hsep hj' hi' h).ne heq.symm)
  have hcount := card_le_card_of_injOn hit
    (fun i hi => (hhit (Nat.lt_succ_iff.mp (mem_range.mp hi))).1) hinj
  rw [card_range] at hcount
  omega

/-- The lower bound follows by applying the walk inequality to the negated values. -/
theorem integer_walk_abs_le {f : ℕ → ℤ} {s : Finset ℤ} (hs : ∀ n, f n ∈ s)
    {D : ℕ} (hstep : ∀ n, |f (n + 1) - f n| ≤ D) (n : ℕ) :
    |f n - f 0| ≤ ((D : ℤ) + 1) * s.card := by
  have hp (i : ℕ) : f (i + 1) ≤ f i + D := by
    have h := (abs_le.mp (hstep i)).2
    omega
  have hq (i : ℕ) : - f (i + 1) ≤ - f i + D := by
    have h := (abs_le.mp (hstep i)).1
    omega
  have hpos := integer_walk_le hs hp n
  have hneg := integer_walk_le (s := s.image fun x => -x)
    (fun i => mem_image.mpr ⟨f i, hs i, rfl⟩) hq n
  have hCard : (s.image fun x => -x).card = s.card :=
    card_image_of_injective _ neg_injective
  rw [hCard] at hneg
  exact abs_le.mpr ⟨by omega, by omega⟩

end Jsp000726
