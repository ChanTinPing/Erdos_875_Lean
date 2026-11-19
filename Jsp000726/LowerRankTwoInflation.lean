module

public import Jsp000726.LowerAsymptoticsRankPrefix
public import Jsp000726.LowerRankTwoBalance
public import Jsp000726.LowerRankTwoFamilies

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726

open Finset

/-- The high window is shorter than the inter-chain spacing and no wider than the available prefix scale. -/
noncomputable def rankTwoWindowHeight (R : ℝ) (L : ℕ) : ℝ :=
  min (R * (L : ℝ)) (R ^ (1 + (3 / 25 : ℝ))) / 10

/-- The two spacing alternatives in the rank-two argument, stated on the numeric carrier. -/
def RankTwoWindowOptions (P : Finset ℕ) (R c v C : ℝ) : Prop :=
  (∀ x ∈ P, ∀ y ∈ P, x < y → (x : ℝ) + R / 10 < (y : ℝ)) ∨
    ∃ (d : ℝ) (L : ℕ), 0 < d ∧ d ≤ R / 10 ∧ 0 < L ∧
      (L : ℝ) ≤ C * d ^ gapMu c v ∧
      (∀ x ∈ P, ∀ y ∈ P, x < y → (x : ℝ) + d ≤ (y : ℝ)) ∧
      ∀ z, (P.filter fun x => x ≤ z ∧ z < x + (⌊rankTwoWindowHeight R L⌋₊ + 1)).card ≤ L

theorem rankTwoWindowHeight_nonneg {R : ℝ} (hR : 0 ≤ R) (L : ℕ) :
    0 ≤ rankTwoWindowHeight R L :=
  div_nonneg (le_min (mul_nonneg hR (Nat.cast_nonneg L)) (Real.rpow_nonneg hR _)) (by norm_num)

theorem rankTwoWindowHeight_le_power {R : ℝ} (hR : 0 ≤ R) (L : ℕ) :
    rankTwoWindowHeight R L ≤ R ^ (1 + (3 / 25 : ℝ)) := by
  unfold rankTwoWindowHeight
  calc
    _ ≤ R ^ (1 + (3 / 25 : ℝ)) / 10 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    _ ≤ _ := div_le_self (Real.rpow_nonneg hR _) (by norm_num)

private theorem rankTwoWindowHeight_pow {R v : ℝ} (hR : 0 < R) (L : ℕ) :
    rankTwoWindowHeight R L ^ v =
      (R ^ v * min (L : ℝ) (R ^ (3 / 25 : ℝ)) ^ v) / (10 : ℝ) ^ v := by
  have hmin : min (R * (L : ℝ)) (R ^ (1 + (3 / 25 : ℝ))) =
      R * min (L : ℝ) (R ^ (3 / 25 : ℝ)) := by
    rw [Real.rpow_add hR, Real.rpow_one]
    by_cases h : (L : ℝ) ≤ R ^ (3 / 25 : ℝ)
    · rw [min_eq_left h, min_eq_left (mul_le_mul_of_nonneg_left h hR.le)]
    · rw [min_eq_right (le_of_not_ge h), min_eq_right (mul_le_mul_of_nonneg_left (le_of_not_ge h) hR.le)]
  unfold rankTwoWindowHeight
  rw [hmin, Real.div_rpow (mul_nonneg hR.le
    (le_min (Nat.cast_nonneg L) (Real.rpow_nonneg hR.le _))) (by norm_num),
    Real.mul_rpow hR.le (le_min (Nat.cast_nonneg L) (Real.rpow_nonneg hR.le _))]

/-- Both rank-two spacing cases give one literal family of the required order, on the same
protected support and in the same span. The coefficient is uniform across both cases. -/
theorem rankTwo_uniform_inflated_family {a : ℕ → ℕ} {P T : Finset ℕ}
    {q b V U m : ℕ} {R c v C A : ℝ}
    (hcl : 4.55 ≤ c) (hcu : c ≤ 4.562) (hv : (0.6 : ℝ) ≤ v) (hvu : v ≤ (c - 1) / c)
    (hR : 1 ≤ R) (hC : 1 ≤ C) (hA : 0 < A)
    (hWT : Disjoint (range (m / 4)) T) (hP : P ⊆ sumLayer a T q)
    (hspan : ∀ p ∈ P, b ≤ p ∧ p ≤ b + V)
    (hbudget : prefixWeight a (m / 4) ≤ U)
    (hfit : ∀ H : ℝ, 0 ≤ H → H ≤ R ^ (1 + (3 / 25 : ℝ)) → 4 * realPrefixAt a H ≤ m)
    (hearly : ∀ H : ℝ, 0 ≤ H → A * H ^ v ≤ (largestLayer a (realPrefixAt a H) : ℝ))
    (hcases : RankTwoWindowOptions P R c v C) :
    ∃ r : ℕ, ∃ X : Finset ℕ, X ⊆ sumLayer a (range (m / 4) ∪ T) r ∧
      (∀ x ∈ X, b ≤ x ∧ x ≤ b + V + U) ∧
      A / (C * (10 : ℝ) ^ v) * (P.card : ℝ) * R ^ rankTwoSigma c v ≤ (X.card : ℝ) := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hCv : 0 < C := zero_lt_one.trans_le hC
  have hv0 : 0 ≤ v := by linarith
  have hvpos : 0 < v := by linarith
  have h10 : 0 < (10 : ℝ) ^ v := by positivity
  have hRC : R ≤ R ^ (1 + (3 / 25 : ℝ)) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hR (show 1 ≤ 1 + (3 / 25 : ℝ) by norm_num)
  let A₀ := A / (10 : ℝ) ^ v
  let M : ℝ := P.card
  have hA₀ : 0 ≤ A₀ := div_nonneg hA.le h10.le
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have chooseEarly (H : ℝ) (hH : 0 ≤ H) (hHR : H ≤ R ^ (1 + (3 / 25 : ℝ))) :
      ∃ r : ℕ,
        A * H ^ v ≤ ((sumLayer a (range (realPrefixAt a H)) r).card : ℝ) ∧
        range (realPrefixAt a H) ⊆ range (m / 4) ∧
        (∑ i ∈ range (realPrefixAt a H), a i) ≤ U := by
    obtain ⟨r, _, heq⟩ := exists_layer_card_eq_largestLayer a (realPrefixAt a H)
    have hsize := hfit H hH hHR
    refine ⟨r, by simpa only [heq] using hearly H hH, range_mono (by omega), ?_⟩
    exact (prefixWeight_mono a (by omega : realPrefixAt a H ≤ m / 4)).trans hbudget
  rcases hcases with hno | ⟨d, L, hd, hdR, hL, hlen, hsmall, hwindows⟩
  · let H := R / 10
    have hH : 0 ≤ H := div_nonneg hR0 (by norm_num)
    have hHR : H ≤ R ^ (1 + (3 / 25 : ℝ)) :=
      (div_le_self hR0 (by norm_num)).trans hRC
    obtain ⟨r, hE, hS, hbudgetH⟩ := chooseEarly H hH hHR
    let S := range (realPrefixAt a H)
    let F := sumLayer a S r
    have hsep : ∀ x ∈ P, ∀ z ∈ P, x < z → x + (⌊H⌋₊ + 1) ≤ z := by
      intro x hx z hz h
      exact nat_window_le_of_real_separation hH (hno x hx z hz h)
    obtain ⟨X, hX, hXspan, hcard⟩ := translated_family_of_spacing
      (hWT.mono hS Subset.rfl) (show F ⊆ sumLayer a S r from Subset.rfl)
      hP hspan hbudgetH (prefixWeight_realPrefixAt_lt_window a H) hsep
    refine ⟨r + q, X, ?_, hXspan, ?_⟩
    · intro x hx
      obtain ⟨Z, hZ, hc, hs⟩ := mem_sumLayer.mp (hX hx)
      exact mem_sumLayer.mpr ⟨Z, hZ.trans (union_subset_union hS Subset.rfl), hc, hs⟩
    have hE' : A₀ * R ^ v ≤ (F.card : ℝ) := by
      calc
        A₀ * R ^ v = A * H ^ v := by
          dsimp [A₀, H]
          rw [Real.div_rpow hR0 (by norm_num)]
          ring
        _ ≤ _ := hE
    have hcoeff : A / (C * (10 : ℝ) ^ v) ≤ A₀ :=
      div_le_div_of_nonneg_left hA.le h10
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC h10.le)
    have hpow := Real.rpow_le_rpow_of_exponent_le hR ((rankTwoSigma_pos_lt hcl hcu hvpos hvu).2.le)
    have hF : A / (C * (10 : ℝ) ^ v) * R ^ rankTwoSigma c v ≤ (F.card : ℝ) :=
      (mul_le_mul hcoeff hpow (Real.rpow_nonneg hR0 _) hA₀).trans hE'
    calc
      _ = M * (A / (C * (10 : ℝ) ^ v) * R ^ rankTwoSigma c v) := by dsimp [M]; ring
      _ ≤ M * (F.card : ℝ) := mul_le_mul_of_nonneg_left hF hM
      _ ≤ _ := by dsimp [M]; rw [mul_comm]; exact_mod_cast hcard
  · let H₁ := d / 4
    let H₂ := rankTwoWindowHeight R L
    have hH₁ : 0 ≤ H₁ := div_nonneg hd.le (by norm_num)
    have hH₁R : H₁ ≤ R ^ (1 + (3 / 25 : ℝ)) := by dsimp [H₁]; linarith only [hdR, hR0, hRC]
    have hH₂ : 0 ≤ H₂ := rankTwoWindowHeight_nonneg hR0 L
    have hH₂R : H₂ ≤ R ^ (1 + (3 / 25 : ℝ)) := rankTwoWindowHeight_le_power hR0 L
    obtain ⟨r₁, hE₁, hS₁, hU₁⟩ := chooseEarly H₁ hH₁ hH₁R
    obtain ⟨r₂, hE₂, hS₂, hU₂⟩ := chooseEarly H₂ hH₂ hH₂R
    let F₁ := sumLayer a (range (realPrefixAt a H₁)) r₁
    let F₂ := sumLayer a (range (realPrefixAt a H₂)) r₂
    have hSep₁ : ∀ x ∈ P, ∀ z ∈ P, x < z → x + (⌊H₁⌋₊ + 1) ≤ z := by
      intro x hx z hz h
      apply nat_window_le_of_real_separation hH₁
      have hdist := hsmall x hx z hz h
      dsimp [H₁]
      linarith only [hd, hdist]
    obtain ⟨r, X, hX, hXspan, hcard₁, hcard₂⟩ := rankTwo_inflated_family
      hS₁ hS₂ hWT (show F₁ ⊆ sumLayer a _ r₁ from Subset.rfl)
      (show F₂ ⊆ sumLayer a _ r₂ from Subset.rfl) hP hspan hU₁ hU₂
      (prefixWeight_realPrefixAt_lt_window a H₁) (prefixWeight_realPrefixAt_lt_window a H₂)
      hSep₁ hwindows
    refine ⟨r, X, hX, hXspan, ?_⟩
    have hcard₁' : (F₁.card : ℝ) * M ≤ (X.card : ℝ) := by
      dsimp [M]; exact_mod_cast hcard₁
    have hcard₂' : (F₂.card : ℝ) * M ≤ (L : ℝ) * (X.card : ℝ) := by
      dsimp [M]; exact_mod_cast hcard₂
    have hL' : 0 < (L : ℝ) := by exact_mod_cast hL
    have hfour : 0 < (4 : ℝ) ^ v := by positivity
    have hfour_le : (4 : ℝ) ^ v ≤ (10 : ℝ) ^ v :=
      Real.rpow_le_rpow (by norm_num) (by norm_num) hv0
    have hcoeff : A₀ ≤ A / (4 : ℝ) ^ v :=
      div_le_div_of_nonneg_left hA.le hfour hfour_le
    have hlow : A₀ * d ^ v ≤ (F₁.card : ℝ) := by
      calc
        _ ≤ (A / (4 : ℝ) ^ v) * d ^ v :=
          mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hd.le _)
        _ = A * H₁ ^ v := by dsimp [H₁]; rw [Real.div_rpow hd.le (by norm_num)]; ring
        _ ≤ _ := hE₁
    let G := R ^ v * min (L : ℝ) (R ^ (3 / 25 : ℝ)) ^ v
    have hhigh : A₀ * G ≤ (F₂.card : ℝ) := by
      calc
        A₀ * G = A * H₂ ^ v := by
          dsimp [A₀, G, H₂]
          rw [rankTwoWindowHeight_pow hRpos L]
          ring
        _ ≤ _ := hE₂
    have hcase₁ : A₀ * M * d ^ v ≤ (X.card : ℝ) := by
      rw [mul_right_comm A₀ M]
      exact (mul_le_mul_of_nonneg_right hlow hM).trans hcard₁'
    have hcase₂ : A₀ * M * (G / (L : ℝ)) ≤ (X.card : ℝ) := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hL').mpr
      rw [mul_right_comm A₀ M, mul_comm (X.card : ℝ)]
      exact (mul_le_mul_of_nonneg_right hhigh hM).trans hcard₂'
    have hmax : A₀ * M * max (d ^ v) (G / (L : ℝ)) ≤ (X.card : ℝ) := by
      rcases le_total (d ^ v) (G / (L : ℝ)) with h | h
      · simpa only [max_eq_right h] using hcase₂
      · simpa only [max_eq_left h] using hcase₁
    have hv' : (3 / 5 : ℝ) ≤ v := by linarith
    have hbal := rank_two_gap_balance hcl hcu hv' hvu hR hL' hd.le hC hlen
    calc
      _ = A₀ * M * (R ^ rankTwoSigma c v / C) := by dsimp [A₀, M]; field_simp
      _ ≤ A₀ * M * max (d ^ v) (G / (L : ℝ)) :=
        mul_le_mul_of_nonneg_left hbal (mul_nonneg hA₀ hM)
      _ ≤ _ := hmax

end Jsp000726
