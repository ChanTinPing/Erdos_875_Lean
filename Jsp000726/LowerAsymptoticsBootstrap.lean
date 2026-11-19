module

public import Jsp000726.LowerAsymptoticsPrefix
public import Jsp000726.LowerAsymptoticsHeavy
public import Jsp000726.LowerEarlyIteration

import Mathlib.Tactic.Linarith

@[expose] public section

namespace Jsp000726

open Filter

/-- The checked uniform moment input used to iterate the initial subset-count estimate. -/
theorem earlyCountMoment_of_early_allCounts
    {a : ℕ → ℕ} (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    {c w : ℝ} (hc : 0 ≤ c) (hw₀ : 0 ≤ w) (hw₁ : w < 1)
    (hgap : ∀ᶠ n : ℕ in atTop, (gap a n : ℝ) ≤ (n + 1 : ℝ) ^ c)
    (hEarly : EarlyPower a (allCounts a) w) : EarlyCountMoment a c w := by
  obtain ⟨C, hC, htail⟩ := heavyCount_bound_of_early_allCounts hw₀ hEarly
  apply prefixWeight_moment_bound_of_tail_and_gaps ha.monotone hpos hc hw₀ hw₁ hC.le hgap
    (fun n => (allCounts a n : ℝ)) _ 8 (fun n H _ hh => htail n H hh)
  intro n
  have hn : (n : ℝ) + 1 ≤ (allCounts a n : ℝ) := by exact_mod_cast succ_le_allCounts ha hpos n
  exact max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith)

end Jsp000726
