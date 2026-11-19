module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace Jsp000726

open Filter

/-- Equal sums over finite sets of distinct indices have equal cardinalities. -/
def Admissible (a : ℕ → ℕ) : Prop :=
  ∀ U V : Finset ℕ, (∑ i ∈ U, a i) = (∑ i ∈ V, a i) → U.card = V.card

/-- The gap at the zero-based index `n`; its paper index is `n + 1`. -/
def gap (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  a (n + 1) - a n

noncomputable def gapThreshold : ℝ :=
  (5 + Real.sqrt 17) / 2

def GapExponent (c : ℝ) : Prop :=
  ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ n, 0 < a n) ∧ Admissible a ∧
    ∀ n : ℕ, (gap a n : ℝ) ≤ (n + 1 : ℝ) ^ c

def EventualGapExponent (c : ℝ) : Prop :=
  ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ n, 0 < a n) ∧ Admissible a ∧
    ∀ᶠ n : ℕ in atTop, (gap a n : ℝ) ≤ (n + 1 : ℝ) ^ c

/-- The explicit all-index gap question from Erdős #875 and JSP-000726. -/
def SharpGapStatement : Prop :=
  {c : ℝ | GapExponent c} = Set.Ici gapThreshold

/-- The eventual-bound formulation used by Formal Conjectures. -/
def SharpEventualGapStatement : Prop :=
  {c : ℝ | EventualGapExponent c} = Set.Ici gapThreshold

theorem GapExponent.eventual {c : ℝ} (h : GapExponent c) : EventualGapExponent c := by
  obtain ⟨a, hmono, hpos, hadm, hgap⟩ := h
  exact ⟨a, hmono, hpos, hadm, Eventually.of_forall hgap⟩

theorem GapExponent.mono {c d : ℝ} (hc : GapExponent c) (hcd : c ≤ d) :
    GapExponent d := by
  obtain ⟨a, hmono, hpos, hadm, hgap⟩ := hc
  refine ⟨a, hmono, hpos, hadm, fun n => (hgap n).trans ?_⟩
  exact Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_left (Nat.cast_nonneg n)) hcd

/-- A sharp all-index witness and universal eventual obstruction settle both conventions. -/
theorem sharpGapStatements_of_bounds (hupper : GapExponent gapThreshold)
    (hlower : ∀ c : ℝ, EventualGapExponent c → gapThreshold ≤ c) :
    SharpGapStatement ∧ SharpEventualGapStatement := by
  constructor
  · ext c
    exact ⟨fun hc => hlower c (GapExponent.eventual hc), hupper.mono⟩
  · ext c
    exact ⟨hlower c, fun hc => (hupper.mono hc).eventual⟩

end Jsp000726
