module

public import Jsp000726.DyadicSixth
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.BigOperators.Fin

import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726.PublicStructure

open Finset

/-- Repackage a rank-two affine generalized progression as an explicit integer
coordinate box, preserving its carrier and properness. -/
private theorem rankTwo_integerGAP_as_box_lengths (P : IntegerGAP) (hr : P.rank = 2)
    (hproper : P.Proper) :
    ∃ (g₁ g₂ : ℤ) (L₁ L₂ : ℕ),
      L₁ = P.length (Fin.cast hr.symm 0) + 1 ∧ L₂ = P.length (Fin.cast hr.symm 1) + 1 ∧
      0 < L₁ ∧ 0 < L₂ ∧
      let S := Ico (0 : ℤ) (L₁ : ℤ) ×ˢ Ico (0 : ℤ) (L₂ : ℤ)
      let f (p : ℤ × ℤ) := P.base + g₁ * p.1 + g₂ * p.2
      P.carrier = S.image f ∧ Set.InjOn f S := by
  obtain ⟨r, b, g, L⟩ := P
  change r = 2 at hr
  subst r
  let P : IntegerGAP := ⟨2, b, g, L⟩
  let L₁ := L 0 + 1
  let L₂ := L 1 + 1
  let S := Ico (0 : ℤ) (L₁ : ℤ) ×ˢ Ico (0 : ℤ) (L₂ : ℤ)
  let f (p : ℤ × ℤ) := b + g 0 * p.1 + g 1 * p.2
  let coord (x : P.Param) : ℤ × ℤ := ((x 0 : ℤ), (x 1 : ℤ))
  have hm (x : P.Param) : coord x ∈ S := by
    refine mem_product.mpr ⟨mem_Ico.mpr ⟨Int.natCast_nonneg _, ?_⟩,
      mem_Ico.mpr ⟨Int.natCast_nonneg _, ?_⟩⟩
    · exact Int.ofNat_lt.mpr (x 0).isLt
    · exact Int.ofNat_lt.mpr (x 1).isLt
  have hcoord (p : ℤ × ℤ) (hp : p ∈ S) : ∃ x : P.Param, coord x = p := by
    have hp₁ := mem_Ico.mp (mem_product.mp hp).1
    have hp₂ := mem_Ico.mp (mem_product.mp hp).2
    have h₁ : (p.1.toNat : ℤ) = p.1 := Int.toNat_of_nonneg hp₁.1
    have h₂ : (p.2.toNat : ℤ) = p.2 := Int.toNat_of_nonneg hp₂.1
    let x₁ : Fin (L 0 + 1) := ⟨p.1.toNat, Int.ofNat_lt.mp (h₁.symm ▸ hp₁.2)⟩
    let x₂ : Fin (L 1 + 1) := ⟨p.2.toNat, Int.ofNat_lt.mp (h₂.symm ▸ hp₂.2)⟩
    let x : P.Param := Fin.cons x₁ (Fin.cons x₂ (fun i => Fin.elim0 i))
    refine ⟨x, Prod.ext ?_ ?_⟩
    · simpa only [coord, x, Fin.cons_zero, x₁] using h₁
    · change ((x ((0 : Fin 1).succ)).val : ℤ) = p.2
      simpa only [x, Fin.cons_succ, Fin.cons_zero, x₂] using h₂
  have he (x : P.Param) : P.eval x = f (coord x) := by
    change b + ∑ i : Fin 2, ((x i).val : ℤ) * g i = b + g 0 * (x 0 : ℤ) + g 1 * (x 1 : ℤ)
    rw [Fin.sum_univ_two]
    ring
  refine ⟨g 0, g 1, L₁, L₂, rfl, rfl, Nat.succ_pos _, Nat.succ_pos _, ?_, ?_⟩
  · change P.carrier = S.image f
    ext z
    constructor
    · intro hz
      obtain ⟨x, _, rfl⟩ := mem_image.mp (show z ∈ (univ : Finset P.Param).image P.eval from hz)
      exact mem_image.mpr ⟨coord x, hm x, (he x).symm⟩
    · intro hz
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hz
      obtain ⟨x, rfl⟩ := hcoord p hp
      exact mem_image.mpr ⟨x, mem_univ _, he x⟩
  · change Set.InjOn f S
    intro p hp q hq hpq
    obtain ⟨x, rfl⟩ := hcoord p hp
    obtain ⟨y, rfl⟩ := hcoord q hq
    have hh : P.eval x = P.eval y := by rw [he, he]; exact hpq
    exact congrArg coord (show x = y from hproper hh)

/-- Repackage a rank-two generalized progression as an explicit integer
coordinate box, preserving its carrier and properness. -/
theorem rankTwo_integerGAP_as_box (P : IntegerGAP) (hr : P.rank = 2) (hproper : P.Proper) :
    ∃ (g₁ g₂ : ℤ) (L₁ L₂ : ℕ), 0 < L₁ ∧ 0 < L₂ ∧
      let S := Ico (0 : ℤ) (L₁ : ℤ) ×ˢ Ico (0 : ℤ) (L₂ : ℤ)
      let f (p : ℤ × ℤ) := P.base + g₁ * p.1 + g₂ * p.2
      P.carrier = S.image f ∧ Set.InjOn f S := by
  obtain ⟨g₁, g₂, L₁, L₂, _, _, h₁, h₂, hc, hp⟩ := rankTwo_integerGAP_as_box_lengths P hr hproper
  exact ⟨g₁, g₂, L₁, L₂, h₁, h₂, hc, hp⟩

/-- Positive side widths give a nondegenerate inclusive box of the same volume,
as needed for the rank-two mean-spacing argument. -/
theorem rankTwo_integerGAP_as_nontrivial_box (P : IntegerGAP) (hr : P.rank = 2)
    (hproper : P.Proper) (hwidth : ∀ i, 0 < P.length i) :
    ∃ (g₁ g₂ : ℤ) (X Y : ℕ), 0 < X ∧ 0 < Y ∧
      let S := Icc (0 : ℤ) (X : ℤ) ×ˢ Icc (0 : ℤ) (Y : ℤ)
      let f (p : ℤ × ℤ) := P.base + g₁ * p.1 + g₂ * p.2
      P.carrier = S.image f ∧ Set.InjOn f S ∧ P.carrier.card = (X + 1) * (Y + 1) := by
  obtain ⟨g₁, g₂, L₁, L₂, hL₁, hL₂, _, _, hc, hp⟩ := rankTwo_integerGAP_as_box_lengths P hr hproper
  let X := P.length (Fin.cast hr.symm (0 : Fin 2))
  let Y := P.length (Fin.cast hr.symm (1 : Fin 2))
  have hseg (n : ℕ) : Ico (0 : ℤ) ((n + 1 : ℕ) : ℤ) = Icc (0 : ℤ) (n : ℤ) := by
    ext x
    simp only [mem_Ico, mem_Icc, Nat.cast_add, Nat.cast_one]
    omega
  change L₁ = X + 1 at hL₁
  change L₂ = Y + 1 at hL₂
  rw [hL₁, hL₂, hseg, hseg] at hc hp
  refine ⟨g₁, g₂, X, Y, hwidth _, hwidth _, hc, hp, ?_⟩
  rw [hc, card_image_of_injOn hp, card_product]
  have hcard (n : ℕ) : (Icc (0 : ℤ) (n : ℤ)).card = n + 1 := by
    rw [Int.card_Icc]
    omega
  rw [hcard, hcard]

end Jsp000726.PublicStructure
