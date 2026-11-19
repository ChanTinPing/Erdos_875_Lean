/-
Adapted from David Loeffler's Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar.
Copyright (c) 2024 David Loeffler. Released under Apache 2.0.
Only the primitive complex-character declarations are retained, with distinct replay names.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Tactic.Ring

public section

open Complex Function
open scoped Real

private noncomputable def replayCircleAddChar {T : ℝ} : AddChar (AddCircle T) Circle where
  toFun := AddCircle.toCircle
  map_zero_eq_one' := AddCircle.toCircle_zero
  map_add_eq_mul' := AddCircle.toCircle_add

namespace ZMod

variable {N : ℕ} [NeZero N]

private noncomputable def replayToCircle : AddChar (ZMod N) Circle :=
  replayCircleAddChar.compAddMonoidHom toAddCircle

noncomputable def replayStdAddChar : AddChar (ZMod N) ℂ :=
  Circle.coeHom.compAddChar replayToCircle

private lemma replayToCircle_intCast (j : ℤ) :
    replayToCircle (j : ZMod N) = exp (2 * π * I * j / N) := by
  rw [replayToCircle, AddChar.compAddMonoidHom_apply, replayCircleAddChar, AddChar.coe_mk,
    AddCircle.toCircle, toAddCircle_intCast, Function.Periodic.lift_coe, Circle.coe_exp]
  push_cast
  ring_nf

set_option backward.isDefEq.respectTransparency.types false in
lemma replayStdAddChar_coe (j : ℤ) :
    replayStdAddChar (j : ZMod N) = exp (2 * π * I * j / N) := by
  simp [replayStdAddChar, replayToCircle_intCast]

lemma isPrimitive_replayStdAddChar (N : ℕ) [NeZero N] :
    (replayStdAddChar (N := N)).IsPrimitive := by
  have hcircle : Injective (replayToCircle : ZMod N → Circle) :=
    (AddCircle.injective_toCircle one_ne_zero).comp (toAddCircle_injective N)
  have hchar : Injective (replayStdAddChar : ZMod N → ℂ) := Subtype.coe_injective.comp hcircle
  refine AddChar.zmod_char_primitive_of_eq_one_only_at_zero _ _ (fun t ht ↦ ?_)
  rwa [← (replayStdAddChar (N := N)).map_zero_eq_one, hchar.eq_iff] at ht

end ZMod
