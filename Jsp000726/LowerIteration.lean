module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

import Mathlib.Tactic.Linarith

@[expose] public section

namespace Jsp000726

/-- A gain valid throughout a left neighborhood of every intermediate exponent
forces the eventually available exponents past the upper endpoint. -/
theorem exists_exponent_gt_of_local_step {P : ℝ → Prop} {a b : ℝ} (base : P a)
    (step : ∀ t ∈ Set.Icc a b, ∃ l < t,
      ∀ v ∈ Set.Icc a t, l < v → P v → ∃ w > t, P w) :
    ∃ w > b, P w := by
  by_contra! hno
  let S : Set ℝ := {x | a ≤ x ∧ P x}
  have haS : a ∈ S := ⟨le_rfl, base⟩
  have hS : S.Nonempty := ⟨a, haS⟩
  have hSb : ∀ x ∈ S, x ≤ b := fun x hx => le_of_not_gt (fun hxb => hno x hxb hx.2)
  have hSbdd : BddAbove S := ⟨b, hSb⟩
  let t := sSup S
  have hat : a ≤ t := le_csSup hSbdd haS
  have htb : t ≤ b := csSup_le hS hSb
  obtain ⟨l, hl, hs⟩ := step t ⟨hat, htb⟩
  obtain ⟨v, hv, hlv⟩ := exists_lt_of_lt_csSup hS hl
  obtain ⟨w, htw, hw⟩ := hs v ⟨hv.1, le_csSup hSbdd hv⟩ hlv hv.2
  exact (not_lt_of_ge (le_csSup hSbdd ⟨hat.trans htw.le, hw⟩)) htw

/-- A continuous, strictly improving exponent map propagates a downward-closed
property to every exponent short of the upper endpoint. -/
theorem all_below_of_continuous_gain {P : ℝ → Prop} {f : ℝ → ℝ} {a b : ℝ}
    (base : P a) (down : Antitone P)
    (cont : ∀ x ∈ Set.Ico a b, ContinuousAt f x)
    (gain : ∀ x ∈ Set.Ico a b, x < f x)
    (step : ∀ x ∈ Set.Ico a b, P x → P (min b (f x))) :
    ∀ u < b, P u := by
  intro u hu
  obtain ⟨w, huw, hw⟩ := exists_exponent_gt_of_local_step (b := u) base (by
    intro t ht
    have htab : t ∈ Set.Ico a b := ⟨ht.1, ht.2.trans_lt hu⟩
    have hgain := gain t htab
    let ε := (f t - t) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨δ, hδ, hclose⟩ := (Metric.continuousAt_iff.mp (cont t htab)) ε hε
    refine ⟨t - δ, by linarith, ?_⟩
    intro v hv hlv hp
    have hvdist : dist v t < δ := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hv.2)]
      linarith
    have hfdist := hclose hvdist
    rw [Real.dist_eq] at hfdist
    have hft : t < f v := by
      have hdiff := (abs_lt.mp hfdist).1
      dsimp [ε] at hdiff
      linarith
    have hvab : v ∈ Set.Ico a b := ⟨hv.1, hv.2.trans_lt htab.2⟩
    exact ⟨min b (f v), lt_min htab.2 hft, step v hvab hp⟩)
  exact down huw.le hw

/-- Strict gain at an endpoint persists for an input taken arbitrarily close
to the endpoint from below. -/
theorem exists_left_of_continuousAt_lt {f : ℝ → ℝ} {a b q : ℝ} (hab : a < b)
    (hcont : ContinuousAt f b) (hq : q < f b) :
    ∃ v ∈ Set.Ioo a b, q < f v := by
  let ε := (f b - q) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨δ, hδ, hclose⟩ := (Metric.continuousAt_iff.mp hcont) ε hε
  let e := min (δ / 2) ((b - a) / 2)
  have he : 0 < e := lt_min (by linarith) (by linarith)
  have he₁ : e ≤ δ / 2 := min_le_left _ _
  have he₂ : e ≤ (b - a) / 2 := min_le_right _ _
  let v := b - e
  have hv : dist v b < δ := by
    rw [Real.dist_eq, show v - b = -e by dsimp [v]; ring, abs_neg, abs_of_pos he]
    linarith
  have hfv := hclose hv
  rw [Real.dist_eq] at hfv
  have hn := (abs_lt.mp hfv).1
  dsimp [ε] at hn
  exact ⟨v, ⟨by dsimp [v]; linarith, by dsimp [v]; linarith⟩, by linarith⟩

end Jsp000726
