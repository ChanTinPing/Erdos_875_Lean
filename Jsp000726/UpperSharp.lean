module

public import Jsp000726.UpperExtensionGaps
public import Jsp000726.UpperParametersStep
public import Jsp000726.UpperSeed

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

@[expose] public section

namespace Jsp000726.Upper

private structure ConstructionState where
  terms : List ℕ
  reference : ℕ
  modulus : ℕ

private def ConstructionState.period (s : ConstructionState) : ℕ :=
  s.modulus / s.reference.gcd s.modulus

private noncomputable def fixedWeight : ℝ := 204 + 455 * (16900 : ℝ) ^ 2

private theorem fixedWeight_nonneg : 0 ≤ fixedWeight := by
  unfold fixedWeight
  positivity

private structure Valid (s : ConstructionState) : Prop where
  length_ge : 2 ≤ s.terms.length
  reference_pos : 0 < s.reference
  modulus_pos : 0 < s.modulus
  period_le : s.period ≤ sharpR s.terms.length
  sorted : s.terms.Pairwise (· < ·)
  positive : ∀ x ∈ s.terms, 0 < x
  below : ∀ x ∈ s.terms, x < s.reference
  last_add : s.terms[s.terms.length - 1]'(by omega) + s.modulus = s.reference
  invariant : Upper.invariant (integerTerms s.terms) s.reference s.modulus s.period
  budget : mass (integerTerms s.terms) s.reference +
    10 * (s.modulus : ℤ) * (s.terms.length : ℤ) ^ 2 < (s.reference : ℤ) * s.period
  small : fixedWeight * ((s.reference : ℝ) / (s.terms.length : ℝ) ^ sharpRho) ≤ 1
  gaps : IndexedGapBound gapThreshold 0 s.terms

private theorem seed_valid {N : ℕ} (hN : 2 ≤ N)
    (hsmall : fixedWeight * ((seedReference N : ℝ) / (N : ℝ) ^ sharpRho) ≤ 1) :
    Valid ⟨seedPrefix N, seedReference N, 1⟩ := by
  have hN0 : 0 < N := by omega
  have hp : (⟨seedPrefix N, seedReference N, 1⟩ : ConstructionState).period = 1 := by
    simp [ConstructionState.period]
  refine {
    length_ge := ?length
    reference_pos := ?reference
    modulus_pos := ?modulus
    period_le := ?period
    sorted := seedPrefix_pairwise N
    positive := fun _ => seedPrefix_positive hN0
    below := fun _ => seedPrefix_lt_reference
    last_add := ?last
    invariant := ?congruence
    budget := ?budget
    small := ?small
    gaps := seedPrefix_gap_bound N
  }
  case length => simpa only [length_seedPrefix] using hN
  case reference => exact hN0.trans_le (Nat.le_add_left _ _)
  case modulus => exact Nat.zero_lt_one
  case period =>
    rw [hp]
    simpa only [length_seedPrefix] using Nat.succ_le_of_lt (hN0.trans_le (le_sharpR hN0))
  case last =>
    simpa only [length_seedPrefix] using seedPrefix_last_add_one hN0
  case congruence =>
    rw [hp]
    exact seedPrefix_invariant N
  case budget =>
    rw [hp]
    simpa only [length_seedPrefix, Nat.cast_one, mul_one] using seedPrefix_budget hN0
  case small => simpa only [length_seedPrefix] using hsmall

private theorem next_state (s : ConstructionState) (hs : Valid s) :
    ∃ t, Valid t ∧ List.IsPrefix s.terms t.terms ∧ s.terms.length < t.terms.length := by
  let a := s.terms
  let B := s.reference
  let h := s.modulus
  let d := s.period
  let N := a.length
  let r := sharpR N
  let K := sharpK r d
  let k := sharpBlock 16900 r
  let R := sharpQ k K
  let H := sharpH N r k R
  let g := B * K
  let B' := B + g * R
  let a' := extendPrefix a B g h N r H R k
  let t : ConstructionState := ⟨a', B', g⟩
  have hN : 0 < N := lt_of_lt_of_le (by decide) hs.length_ge
  have hd : 0 < d := Nat.div_gcd_pos_of_pos_right B hs.modulus_pos
  have hdr : d ≤ r := hs.period_le
  have hr := sharpR_pos hN
  have hNr := le_sharpR hN
  obtain ⟨hKlow, _⟩ := sharpK_bounds hd hdr
  have hK : 0 < K := (Nat.zero_le _).trans_lt hKlow
  have hKk : 2 * K ≤ k := two_mul_sharpK_le_block (by decide) hd hdr
  have hKk' : K ≤ k := by omega
  have hk : 0 < k := hK.trans_le hKk'
  have hkR : k ≤ R := by
    have hq : 2 * k < R := two_mul_lt_sharpQ hK hKk'
    omega
  have hsize : N + r ≤ k := add_le_sharpBlock hr hNr (by decide)
  have hrk : r ^ 2 ≤ k := by
    unfold k sharpBlock
    exact Nat.le_mul_of_pos_left _ (by decide)
  obtain ⟨hH, hEnd⟩ := sharpH_pos_and_end hN (sharpR_le_sq hN) hK hKk' hrk
  have hdK : d ∣ K := sharpK_dvd r d
  have hdiv : h ∣ g := dvd_step_of_period_dvd hdK
  have hg : 0 < g := Nat.mul_pos hs.reference_pos hK
  have hgn : h * N ≤ g :=
    old_step_mul_le_new_step hN (Nat.le_of_dvd hK hdK) hs.budget
  have hhg : h ≤ g := (Nat.le_mul_of_pos_right _ hN).trans hgn
  have hHcap : g * H ≤ B' := by
    have hHR : H ≤ R := calc
      H ≤ r ^ 3 / N ^ 3 + H := Nat.le_add_left _ _
      _ = R - k := hEnd
      _ ≤ R := Nat.sub_le _ _
    exact (Nat.mul_le_mul_left g hHR).trans (Nat.le_add_left _ _)
  have hB' : 0 < B' := hs.reference_pos.trans_le (Nat.le_add_right _ _)
  obtain ⟨hinv, hbudget⟩ := concrete_extend_prefix hs.length_ge hs.reference_pos
    hs.modulus_pos hd hdK hdiv hNr hKlow.le hsize hkR hH hEnd
    (sharpReference_bounds hK hKk).1 hs.below hs.invariant hs.budget
  have hlen : a'.length = N + r + k := length_extendPrefix _ _ _ _ _ _ _ _ _
  have hd' : t.period = K := next_period_eq hs.reference_pos
  have ha'0 : 0 < a'.length := by omega
  have ⟨hgReal, hB'Real⟩ := sharp_step_real_bounds (N := N) (B := B) (C := 16900)
    (by decide) hd hdr
  have hcontract : (B' : ℝ) / (a'.length : ℝ) ^ sharpRho ≤
      ((B : ℝ) / (N : ℝ) ^ sharpRho) / 2 := by
    rw [hlen]
    exact sharp_step_contract (B := B) hN hd hdr
  have hcurrent_nonneg : 0 ≤ ((B : ℝ) / (N : ℝ) ^ sharpRho) := by positivity
  have hsmall : fixedWeight * ((B' : ℝ) / (a'.length : ℝ) ^ sharpRho) ≤ 1 := by
    apply (mul_le_mul_of_nonneg_left hcontract fixedWeight_nonneg).trans
    exact (mul_le_mul_of_nonneg_left (by linarith) fixedWeight_nonneg).trans hs.small
  refine ⟨t, ?_, ?_, ?_⟩
  · refine {
      length_ge := ?length
      reference_pos := hB'
      modulus_pos := hg
      period_le := ?period
      sorted := extendPrefix_pairwise hs.sorted hs.below hN hs.modulus_pos hg hgn hH hEnd
      positive := fun _ => extendPrefix_positive hs.positive hs.reference_pos
      below := ?below
      last_add := extendPrefix_last_add_step hkR hk
      invariant := ?congruence
      budget := ?budget
      small := hsmall
      gaps := ?gaps
    }
    case length =>
      change 2 ≤ a'.length
      rw [hlen]
      exact hs.length_ge.trans (by dsimp [N, a]; omega)
    case period =>
      rw [hd']
      have hklen : k ≤ a'.length := by rw [hlen]; omega
      exact (hKk'.trans hklen).trans (le_sharpR ha'0)
    case below =>
      intro x hx
      have hcap := extendPrefix_le_reference_sub_step hs.below hN hs.modulus_pos
        hgn hH hEnd hkR hk hx
      exact lt_of_lt_of_le (Nat.lt_add_of_pos_right hg) hcap
    case congruence =>
      rw [hd']
      exact hinv
    case budget =>
      rw [hd']
      exact hbudget
    case gaps =>
      exact extendPrefix_gap_bound hN hr hH hhg hEnd (rpow_le_sharpR N)
        (sharpR_le_two_rpow hN) hHcap hgReal (by simpa only [Nat.cast_ofNat] using hB'Real)
        hs.small hs.gaps hs.last_add
  · exact ⟨fillerBlock B g h N r H ++ denseBlock B g R k,
      by simp only [t, a', extendPrefix, List.append_assoc, a]⟩
  · change N < a'.length
    rw [hlen]
    omega

/-- There is an infinite admissible sequence achieving the critical exponent with
coefficient one at every positive index. -/
theorem gapExponent_gapThreshold : GapExponent gapThreshold := by
  obtain ⟨N, hN, hsmall⟩ := exists_normalized_seed fixedWeight fixedWeight_nonneg
  let seed : ConstructionState := ⟨seedPrefix N, seedReference N, 1⟩
  apply gapExponent_of_extension gapThreshold Valid ConstructionState.terms seed
    (seed_valid hN hsmall) next_state (fun _ hs => hs.sorted) (fun _ hs => hs.positive) ?_
    (fun _ hs => hs.gaps)
  intro s hs U V hU hV he
  have hp : 0 < s.period := Nat.div_gcd_pos_of_pos_right _ hs.modulus_pos
  exact hs.invariant.card_eq_of_sum_eq (by exact_mod_cast hs.reference_pos)
    (by exact_mod_cast hp) (by
      have hbudget := hs.budget
      have hnonneg : 0 ≤ 10 * (s.modulus : ℤ) * (s.terms.length : ℤ) ^ 2 := by positivity
      exact (le_add_of_nonneg_right hnonneg).trans_lt hbudget)
    hU hV he

/-- Every exponent at or above the threshold has an all-index witness. -/
theorem gapExponent_of_threshold_le {c : ℝ} (hc : gapThreshold ≤ c) : GapExponent c :=
  gapExponent_gapThreshold.mono hc

end Jsp000726.Upper
