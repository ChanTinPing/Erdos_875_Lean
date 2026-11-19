module

public import Jsp000726.LowerEarlyCounts
public import Jsp000726.LowerEarlyAlgebra

@[expose] public section

namespace Jsp000726

open Finset

/-- A polynomial lower bound, with the natural scale `n + 1`. -/
def PrefixPower (Y : ℕ → ℕ) (u : ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, A * ((n : ℝ) + 1) ^ u ≤ (Y n : ℝ)

/-- A polynomial lower bound at the last prefix of weight at most `x`. -/
def EarlyPower (a Y : ℕ → ℕ) (v : ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ x : ℕ, 1 ≤ x → A * (x : ℝ) ^ v ≤ (Y (prefixAt a x) : ℝ)

theorem earlyPower_antitone (a Y : ℕ → ℕ) : Antitone (EarlyPower a Y) := by
  intro u v huv
  rintro ⟨A, hA, h⟩
  refine ⟨A, hA, fun x hx => ?_⟩
  exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hx) huv) hA.le).trans (h x hx)

/-- The first assertion of manuscript Lemma 3.1, with an explicit uniform constant. -/
theorem prefixPower_allCounts_of_middleLayer {a : ℕ → ℕ} (ha : Admissible a)
    {u : ℝ} (hu : 0 ≤ u) (hW : PrefixPower (middleLayer a) u) :
    PrefixPower (allCounts a) (u + 1) := by
  obtain ⟨A, hA, hW⟩ := hW
  refine ⟨A / (2 : ℝ) ^ (u + 1), div_pos hA (Real.rpow_pos_of_pos (by norm_num) _), fun n => ?_⟩
  have hN : (((n : ℝ) + 1) / 2) ≤ ((n / 2 : ℕ) : ℝ) + 1 := by
    have h : n + 1 ≤ 2 * (n / 2 + 1) := by omega
    have hc : (n : ℝ) + 1 ≤ 2 * (((n / 2 : ℕ) : ℝ) + 1) := by exact_mod_cast h
    linarith
  have hM : (((n : ℝ) + 1) / 2) ≤ ((n - n / 2 + 1 : ℕ) : ℝ) := by
    have h : n + 1 ≤ 2 * (n - n / 2 + 1) := by omega
    have hc : (n : ℝ) + 1 ≤ 2 * ((n - n / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast h
    linarith
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hp := Real.rpow_le_rpow (show (0 : ℝ) ≤ ((n : ℝ) + 1) / 2 by positivity) hN hu
  have hpart : A * (((n : ℝ) + 1) / 2) ^ u ≤ (middleLayer a (n / 2) : ℝ) :=
    (mul_le_mul_of_nonneg_left hp hA.le).trans (hW (n / 2))
  have hcount : (middleLayer a (n / 2) : ℝ) * ((n - n / 2 + 1 : ℕ) : ℝ) ≤ (allCounts a n : ℝ) := by
    exact_mod_cast middleLayer_half_mul_le_allCounts ha n
  calc
    A / (2 : ℝ) ^ (u + 1) * ((n : ℝ) + 1) ^ (u + 1) =
        (A * (((n : ℝ) + 1) / 2) ^ u) * (((n : ℝ) + 1) / 2) := by
      calc
        _ = A * ((((n : ℝ) + 1) ^ (u + 1)) / (2 : ℝ) ^ (u + 1)) := by ring
        _ = A * ((((n : ℝ) + 1) / 2) ^ (u + 1)) := by
          rw [Real.div_rpow hn.le (by norm_num)]
        _ = _ := by
          rw [Real.rpow_add (show (0 : ℝ) < ((n : ℝ) + 1) / 2 by positivity), Real.rpow_one, mul_assoc]
    _ ≤ (middleLayer a (n / 2) : ℝ) * ((n - n / 2 + 1 : ℕ) : ℝ) :=
      mul_le_mul hpart hM (by positivity) (by positivity)
    _ ≤ (allCounts a n : ℝ) := hcount

theorem prefixPower_largestLayer_of_middleLayer {a : ℕ → ℕ} {u : ℝ}
    (h : PrefixPower (middleLayer a) u) : PrefixPower (largestLayer a) u := by
  obtain ⟨A, hA, h⟩ := h
  refine ⟨A, hA, fun n => (h n).trans ?_⟩
  exact_mod_cast middleLayer_le_largestLayer a n

/-- Turning a prefix-weight cap into an initial estimate for the early counting bootstrap. -/
theorem earlyPower_of_prefixPower {a Y : ℕ → ℕ} (hpos : ∀ i, 0 < a i) {b u : ℝ}
    (hb : 0 < b) (hu : 0 < u) (hY : PrefixPower Y u)
    (hweight : ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ,
      (prefixWeight a (n + 1) : ℝ) ≤ D * ((n : ℝ) + 1) ^ b) : EarlyPower a Y (u / b) := by
  obtain ⟨A, hA, hY⟩ := hY
  obtain ⟨D, hD, hweight⟩ := hweight
  refine ⟨A / D ^ (u / b), div_pos hA (Real.rpow_pos_of_pos hD _), fun x _ => ?_⟩
  let n := prefixAt a x
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hx' : (x : ℝ) ≤ D * ((n : ℝ) + 1) ^ b :=
    (show (x : ℝ) ≤ (prefixWeight a (n + 1) : ℝ) by
      exact_mod_cast (prefixAt_lt_prefixWeight_succ hpos x).le).trans (hweight n)
  have hpow := Real.rpow_le_rpow (show (0 : ℝ) ≤ (x : ℝ) by positivity) hx' (div_nonneg hu.le hb.le)
  rw [Real.mul_rpow hD.le (Real.rpow_nonneg hn.le _), ← Real.rpow_mul hn.le,
    show b * (u / b) = u by field_simp] at hpow
  calc
    A / D ^ (u / b) * (x : ℝ) ^ (u / b) ≤ A * ((n : ℝ) + 1) ^ u := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (Real.rpow_pos_of_pos hD _)).2
      have hh := mul_le_mul_of_nonneg_left hpow hA.le
      convert hh using 1
      ring
    _ ≤ (Y n : ℝ) := hY n

/-- Combine the large-prefix and small-prefix branches of the early growth estimate. -/
theorem earlyPower_of_two_branches {a Y : ℕ → ℕ} (hpos : ∀ i, 0 < a i)
    {c α u r : ℝ} (hc : 0 < c) (hα : 0 < α) (hu : 0 < u) (hr : 0 ≤ r)
    (hY : PrefixPower Y u)
    (hnext : ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ,
      (prefixWeight a (n + 1) : ℝ) ≤ D * max (max 1 (prefixWeight a n : ℝ)) (((n : ℝ) + 1) ^ c))
    (hM : ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
      (max 1 (prefixWeight a n : ℝ)) ^ α ≤ K * (Y n : ℝ) * ((n : ℝ) + 1) ^ r) :
    EarlyPower a Y (min (α / (1 + r / u)) (u / c)) := by
  obtain ⟨A, hA, hY⟩ := hY
  obtain ⟨D, hD, hnext⟩ := hnext
  obtain ⟨K, hK, hM⟩ := hM
  let γ := 1 + r / u
  let Q := (D ^ α * K * A⁻¹ ^ (r / u))⁻¹ ^ γ⁻¹
  let R := A / D ^ (u / c)
  have hQ : 0 < Q := Real.rpow_pos_of_pos (inv_pos.mpr
    (mul_pos (mul_pos (Real.rpow_pos_of_pos hD _) hK) (Real.rpow_pos_of_pos (inv_pos.mpr hA) _))) _
  have hR : 0 < R := div_pos hA (Real.rpow_pos_of_pos hD _)
  refine ⟨min Q R, lt_min hQ hR, fun x hx => ?_⟩
  let n := prefixAt a x
  let p : ℝ := (n : ℝ) + 1
  let S : ℝ := max 1 (prefixWeight a n : ℝ)
  have hp : 0 < p := by dsimp [p]; positivity
  have hS : 0 < S := zero_lt_one.trans_le (le_max_left _ _)
  have hx0 : (0 : ℝ) ≤ x := by positivity
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hnext' : (x : ℝ) ≤ D * max S (p ^ c) :=
    (show (x : ℝ) ≤ (prefixWeight a (n + 1) : ℝ) by
      exact_mod_cast (prefixAt_lt_prefixWeight_succ hpos x).le).trans (hnext n)
  rcases le_total (p ^ c) S with h | h
  · rw [max_eq_left h] at hnext'
    have hxα := Real.rpow_le_rpow hx0 hnext' hα.le
    rw [Real.mul_rpow hD.le hS.le] at hxα
    have hm : (x : ℝ) ^ α ≤ (D ^ α * K) * (Y n : ℝ) * p ^ r := by
      have hh := hxα.trans (mul_le_mul_of_nonneg_left (hM n) (Real.rpow_nonneg hD.le _))
      convert hh using 1
      ring
    have hpow := lower_power_of_two_scales hx0 hp hA (mul_pos (Real.rpow_pos_of_pos hD _) hK) hu hr (hY n) hm
    have he := Real.rpow_le_rpow_of_exponent_le hx1 (min_le_left (α / γ) (u / c))
    exact (mul_le_mul (min_le_left Q R) he (Real.rpow_nonneg hx0 _) hQ.le).trans hpow
  · rw [max_eq_right h] at hnext'
    have hxγ := Real.rpow_le_rpow hx0 hnext' (div_nonneg hu.le hc.le)
    rw [Real.mul_rpow hD.le (Real.rpow_nonneg hp.le _), ← Real.rpow_mul hp.le,
      show c * (u / c) = u by field_simp] at hxγ
    have hsmall : R * (x : ℝ) ^ (u / c) ≤ (Y n : ℝ) := by
      dsimp [R]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (Real.rpow_pos_of_pos hD _)).2
      have hh := mul_le_mul_of_nonneg_left hxγ hA.le
      calc
        A * (x : ℝ) ^ (u / c) ≤ A * (D ^ (u / c) * p ^ u) := hh
        _ = (A * p ^ u) * D ^ (u / c) := by ring
        _ ≤ (Y n : ℝ) * D ^ (u / c) := mul_le_mul_of_nonneg_right (hY n) (Real.rpow_nonneg hD.le _)
    have he := Real.rpow_le_rpow_of_exponent_le hx1 (min_le_right (α / γ) (u / c))
    exact (mul_le_mul (min_le_right Q R) he (Real.rpow_nonneg hx0 _) hR.le).trans hsmall

end Jsp000726
