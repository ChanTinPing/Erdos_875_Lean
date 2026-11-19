module

public import Jsp000726.LowerRankAssembly
public import Jsp000726.LowerRankTwoProtectedCounts
public import Jsp000726.LowerRankTwoProtectedPrefix
public import Jsp000726.LowerRankTwoSpacing
public import Jsp000726.LowerRankTwoInflation
public import Jsp000726.LowerRankTwoCarrier
public import Jsp000726.OriginalStatement

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726

open Finset Filter PublicStructure

/-- The finite spacing alternatives before the protected-prefix estimate supplies
the length bound on a short-direction chain. -/
def RawRankTwoOptions (a : ℕ → ℕ) (T Q : Finset ℕ) (q : ℕ) (R : ℝ) : Prop :=
  (∀ x ∈ Q, ∀ y ∈ Q, x < y → (x : ℝ) + R / 10 < (y : ℝ)) ∨
    ∃ d L b : ℕ, 0 < d ∧ (d : ℝ) ≤ R / 10 ∧ 2 ≤ L ∧ ProgressionInLayer a T q b d L ∧
      (∀ x ∈ Q, ∀ y ∈ Q, x < y → (x : ℝ) + (d : ℝ) ≤ (y : ℝ)) ∧
      ∀ z : ℕ, ∀ H : ℝ, 0 ≤ H → H < (7 / 40 : ℝ) * R * (L : ℝ) →
        (Q.filter fun x => x ≤ z ∧ z < x + (⌊H⌋₊ + 1)).card ≤ L

/-- A translated box represented by its natural-number carrier, with exact span. -/
def RankTwoNaturalCarrier (a : ℕ → ℕ) (n : ℕ) (P : IntegerGAP) : Prop :=
  let T := oppositeSupport (n / 2) (n / 16)
  ∃ (Q : Finset ℕ) (b V : ℕ),
    Q.card = P.carrier.card ∧ 0 < V ∧ Q ⊆ sumLayer a T (n / 16) ∧
    (∀ x ∈ Q, b ≤ x ∧ x ≤ b + V) ∧ b + V ∈ Q ∧
    RawRankTwoOptions a T Q (n / 16) ((V : ℝ) / (Q.card : ℝ))

private theorem rankTwoSpan_le_prefixWeight {a : ℕ → ℕ} {n b V r : ℕ} {T Q : Finset ℕ}
    (hT : T ⊆ range n) (hQ : Q ⊆ sumLayer a T r) (hmax : b + V ∈ Q) :
    V ≤ prefixWeight a n := by
  obtain ⟨U, hU, _, hsum⟩ := mem_sumLayer.mp (hQ hmax)
  have hBound : (∑ i ∈ U, a i) ≤ prefixWeight a n :=
    sum_le_sum_of_subset (hU.trans hT)
  omega

private theorem rankTwoVolume_lower {a : ℕ → ℕ} {n C : ℕ} {P : IntegerGAP}
    (hC : 0 < C) (hn : 16 ≤ n) (hP : P.rank = 2) (hW : OppositeLayerWitness a n C P) :
    ((32 : ℝ) ^ (3 : ℕ) * (C : ℝ))⁻¹ * ((n : ℝ) + 1) ^ (3 : ℝ) ≤ (P.carrier.card : ℝ) := by
  have hscale : n + 1 ≤ 32 * (n / 16) := by omega
  have hcard : (n / 16) ^ (3 : ℕ) ≤ C * P.carrier.card := by
    simpa only [hP, Nat.reduceAdd] using hW.2.2.1
  have hpow : (n + 1 : ℕ) ^ (3 : ℕ) ≤ 32 ^ (3 : ℕ) * C * P.carrier.card := calc
    _ ≤ (32 * (n / 16)) ^ (3 : ℕ) := Nat.pow_le_pow_left hscale _
    _ = 32 ^ (3 : ℕ) * (n / 16) ^ (3 : ℕ) := mul_pow _ _ _
    _ ≤ _ := by rw [mul_assoc]; exact Nat.mul_le_mul_left _ hcard
  rw [inv_mul_eq_div, Real.rpow_ofNat]
  apply (div_le_iff₀ (show 0 < (32 : ℝ) ^ (3 : ℕ) * (C : ℝ) by positivity)).2
  rw [mul_comm ((P.carrier.card : ℕ) : ℝ)]
  exact_mod_cast hpow

private theorem rankTwoWindowOptions_of_raw {a : ℕ → ℕ} {T Q : Finset ℕ} {q : ℕ}
    {R c v C K : ℝ} (hR : 0 < R) (hCK : K ≤ C)
    (hraw : RawRankTwoOptions a T Q q R)
    (hlen : ∀ {d L b : ℕ}, 0 < d → 2 ≤ L → ProgressionInLayer a T q b d L →
      (L : ℝ) ≤ K * (d : ℝ) ^ gapMu c v) :
    RankTwoWindowOptions Q R c v C := by
  rcases hraw with h | ⟨d, L, b, hd, hdR, hL, hap, hsep, hWindow⟩
  · exact Or.inl h
  · have hLp : 0 < L := by omega
    have hH := rankTwoWindowHeight_nonneg hR.le L
    have hsmall : rankTwoWindowHeight R L < (7 / 40 : ℝ) * R * (L : ℝ) := by
      unfold rankTwoWindowHeight
      have hp : 0 < R * (L : ℝ) := mul_pos hR (Nat.cast_pos.mpr hLp)
      have hh := div_le_div_of_nonneg_right (min_le_left (R * (L : ℝ))
        (R ^ (1 + (3 / 25 : ℝ)))) (show (0 : ℝ) ≤ 10 by norm_num)
      apply hh.trans_lt
      linarith only [hp]
    refine Or.inr ⟨(d : ℝ), L, Nat.cast_pos.mpr hd, hdR, hLp, ?_, hsep, fun z => hWindow z _ hH hsmall⟩
    exact (hlen hd hL hap).trans
      (mul_le_mul_of_nonneg_right hCK (Real.rpow_nonneg (Nat.cast_nonneg d) _))

/-- Assemble the refined rank-two bound using the finite proper-box geometry. -/
theorem refinedRankTwoGain_of_natural_carrier {a : ℕ → ℕ} {c : ℝ}
    (hmono : StrictMono a) (hpos : ∀ i, 0 < a i) (ha : Admissible a)
    (hcl : 4.55 ≤ c) (hcu : c ≤ 4.562)
    (hgap : ∀ᶠ n : ℕ in atTop, (gap a n : ℝ) ≤ (n + 1 : ℝ) ^ c)
    (hcarrier : ∀ n C : ℕ, 16 ≤ n → 0 < C → ∀ P : IntegerGAP, P.rank = 2 →
      OppositeLayerWitness a n C P → RankTwoNaturalCarrier a n P) :
    RefinedRankTwoGain a c := by
  intro u v w hu₁ huc hv₁ hv _ _ hw hW C hC
  have hc : 0 < c := by linarith
  have hu : 0 < u := by linarith
  have hv₀ : 0 < v := by linarith
  have hvu : v ≤ (c - 1) / c :=
    hv.le.trans (div_le_div_of_nonneg_right (by linarith) hc.le)
  have hB : 0 < c + 2 := by linarith
  have hU : 0 < u + 1 := by linarith
  let D : ℝ := ((32 : ℝ) ^ (3 : ℕ) * (C : ℝ))⁻¹
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨A, hA, hEarly⟩ := earlyPower_real_nonnegative (one_le_largestLayer a) hv₀.le
    (early_largestLayer_of_eventual_gaps hmono hpos ha hc hu huc hW hgap hv₀ hv)
  obtain ⟨B, hBpos, hLength⟩ :=
    progression_length_bound_of_eventual_gaps hmono hpos ha hc hu huc hv₀ hv hW hgap
  let K := max 1 B
  have hK : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  let E := A / (K * (10 : ℝ) ^ v)
  have hE : 0 < E := div_pos hA (mul_pos hKpos (Real.rpow_pos_of_pos (by norm_num) _))
  obtain ⟨G₀, hG₀, hbound⟩ := polynomialTermBound_of_eventual_gaps hmono.monotone hc.le hgap
  have hterm : ∃ G : ℝ, 0 < G ∧ ∀ n : ℕ, (a n : ℝ) ≤ G * ((n : ℝ) + 1) ^ (c + 1) :=
    ⟨G₀, hG₀, fun n => by simpa only [Nat.cast_add, Nat.cast_one] using hbound n⟩
  obtain ⟨G, hG, hPrefix⟩ := prefixWeightCap_to_pointwise
    (prefixWeightCap_of_termCap (by linarith : 0 ≤ c + 1) hterm)
  have hPrefix' (n : ℕ) : (prefixWeight a n : ℝ) ≤ G * (n : ℝ) ^ (c + 2) := by
    simpa only [show c + 1 + 1 = c + 2 by ring] using hPrefix n
  obtain ⟨M₀, hM₀, hProtected⟩ := exists_rankTwo_protected_prefix hpos hG hB hPrefix'
  obtain ⟨hβ, hneg⟩ := rankTwo_support_exponents hcl hcu hu₁ (by linarith)
  have hFit := eventually_four_mul_realPrefixAt_le_protected hB hU
    (by norm_num : (-1 : ℝ) ≤ 3 / 25) hβ hneg hG hD hM₀
    (prefixPower_allCounts_of_middleLayer ha hu.le hW)
  have hSpacing := eventually_rankTwo_spacing_ge hB hD hM₀ 1
  apply oppositeRankGain_two_of_count_bounds hcl hcu hv₀ hvu hw hC hM₀
    (div_pos hE (by norm_num : (0 : ℝ) < 6)) hE
  filter_upwards [eventually_ge_atTop (16 : ℕ), hFit, hSpacing] with n hn hFit hSpacing
  intro P hP hWitness
  obtain ⟨Q, b, V, hcard, hV, hQ, hSpan, hmax, hRaw⟩ := hcarrier n C hn hC P hP hWitness
  let T := oppositeSupport (n / 2) (n / 16)
  let R := (V : ℝ) / (Q.card : ℝ)
  have hT : T ⊆ range n := oppositeSupport_subset_range (by omega)
  have hVn := rankTwoSpan_le_prefixWeight hT hQ hmax
  have hVupper : (V : ℝ) ≤ G * (n : ℝ) ^ (c + 2) :=
    (Nat.cast_le.mpr hVn).trans (hPrefix' n)
  obtain ⟨m, hm, hBudget, hM⟩ := hProtected hVupper
  have hTm : Disjoint (range m) T := disjoint_range_oppositeSupport (by omega)
  have hTquarter : Disjoint (range (n / 4)) T := disjoint_range_oppositeSupport (by omega)
  have hTmquarter : Disjoint (range (m / 4)) T := disjoint_range_oppositeSupport (by omega)
  obtain ⟨hMle, hpack⟩ := rankTwo_initial_packing ha hTm.symm hQ hSpan
    (show prefixWeight a m ≤ V by omega)
  have hVolume : D * ((n : ℝ) + 1) ^ (3 : ℝ) ≤ (Q.card : ℝ) := by
    rw [hcard]
    exact rankTwoVolume_lower hC hn hP hWitness
  have hQpos : 0 < (Q.card : ℝ) :=
    (mul_pos hD (Real.rpow_pos_of_pos (by positivity) _)).trans_le hVolume
  have hR : 1 ≤ R := hSpacing (by exact_mod_cast hMle) hVolume hM (by exact_mod_cast hpack)
  have hVpos : 0 < (V : ℝ) := Nat.cast_pos.mpr hV
  have hVupper' : (V : ℝ) ≤ G * ((n : ℝ) + 1) ^ (c + 2) := hVupper.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg n)
      (le_add_of_nonneg_right zero_le_one) hB.le) hG.le)
  have hCuts : ∀ H : ℝ, 0 ≤ H → H ≤ R ^ (1 + (3 / 25 : ℝ)) →
      4 * realPrefixAt a H ≤ m :=
    fun H hH hHR => hFit _ _ m H hVpos hQpos hR hH hHR hM hVupper' hVolume
  have hcase : RankTwoWindowOptions Q R c v K := rankTwoWindowOptions_of_raw
    (zero_lt_one.trans_le hR) (le_max_right _ _) hRaw
    (fun hd hL hAP => hLength hd hL hT hTquarter hAP)
  let U := prefixWeight a (m / 4)
  obtain ⟨r, X, hX, hXspan, hXcard⟩ := rankTwo_uniform_inflated_family hcl hcu
    (by linarith : (0.6 : ℝ) ≤ v) hvu hR hK hA hTmquarter hQ hSpan
    (show prefixWeight a (m / 4) ≤ U from le_rfl) hCuts hEarly hcase
  have hSup : range (m / 4) ∪ T ⊆ range n :=
    union_subset (range_subset_range.mpr (by omega)) hT
  have hSize : (range (m / 4) ∪ T).card ≤ n / 2 := by
    apply (card_union_le _ _).trans
    rw [card_range, oppositeSupport_card]
    omega
  have hPadding := card_family_le_middleLayer hSup hSize hX
  have hUbudget : V + U ≤ V + prefixWeight a m :=
    Nat.add_le_add_left (prefixWeight_mono a (Nat.div_le_self m 4)) _
  have hMpos : 0 < P.carrier.card := by
    have hPos := Nat.cast_pos.mp hQpos
    rwa [hcard] at hPos
  apply rankTwoCountBounds_of_inflated_family ha hMpos hV (by omega : 2 * (m / 4) ≤ m)
    hTm.symm hX (fun x hx => by simpa only [Nat.add_assoc] using hXspan x hx)
    hUbudget hBudget hM ?_ hPadding
  simpa only [E, R, hcard] using hXcard

private theorem rankTwoNaturalCarrier_of_opposite {a : ℕ → ℕ} {n C : ℕ} {P : IntegerGAP}
    (hn : 16 ≤ n) (hr : P.rank = 2) (h : OppositeLayerWitness a n C P) :
    RankTwoNaturalCarrier a n P := by
  obtain ⟨Q, b, V, hcard, hQ, _, hlast, hV, hSpan, hCases⟩ := opposite_rankTwo_carrier hn hr h
  refine ⟨Q, b, V, hcard, hV, hQ, hSpan, hlast, ?_⟩
  rcases hCases with h | ⟨d, L, B, hd, hdR, hL, hap, _, hGap, hWindow⟩
  · exact Or.inl h
  · refine Or.inr ⟨d, L, B, hd, hdR, hL, hap, ?_, fun z H hH hR => hWindow H hH hR z⟩
    intro x hx y hy hxy
    have hg := hGap x hx y hy hxy
    exact_mod_cast hg

/-- The entire refined rank-two layer gain, including the short-direction case. -/
theorem refinedRankTwoGain_of_eventual_gaps {a : ℕ → ℕ} {c : ℝ}
    (hmono : StrictMono a) (hpos : ∀ i, 0 < a i) (ha : Admissible a)
    (hcl : 4.55 ≤ c) (hcu : c ≤ 4.562)
    (hgap : ∀ᶠ n : ℕ in atTop, (gap a n : ℝ) ≤ (n + 1 : ℝ) ^ c) : RefinedRankTwoGain a c := by
  apply refinedRankTwoGain_of_natural_carrier hmono hpos ha hcl hcu hgap
  exact fun _ _ hn _ _ hr h => rankTwoNaturalCarrier_of_opposite hn hr h

/-- All problem-specific steps of the all-index and eventual classifications are
kernel-checked. Their remaining input is the dyadic subset-sum progression theorem. -/
theorem sharpGapStatements_of_dyadic (hstructure : DyadicSubsetStructure) :
    SharpGapStatement ∧ SharpEventualGapStatement := by
  apply sharpGapStatements_of_dyadic_and_refined_rank_two hstructure
  intro _ _ hmono hpos ha hcl hcu hgap
  exact refinedRankTwoGain_of_eventual_gaps hmono hpos ha hcl
    (hcu.le.trans gapThreshold_lt_4562.le) hgap

/-- The same classification in the original set formulation, including the
Formal Conjectures convention for the eventual gap bound. -/
theorem sharpOriginalGapStatements_of_dyadic (hstructure : DyadicSubsetStructure) :
    {c : ℝ | OriginalGapExponent c} = Set.Ici ((5 + Real.sqrt 17) / 2) ∧
    {c : ℝ | OriginalEventualGapExponent c} = Set.Ici ((5 + Real.sqrt 17) / 2) := by
  apply sharpOriginalGapStatements_of_bounds Upper.gapExponent_gapThreshold
  intro c hc
  have hset := (sharpGapStatements_of_dyadic hstructure).2
  change {c : ℝ | EventualGapExponent c} = Set.Ici gapThreshold at hset
  have hmem : c ∈ {c : ℝ | EventualGapExponent c} := hc
  rw [hset] at hmem
  exact hmem

end Jsp000726
