module

public import Jsp000726.LowerEarlyGrowth
public import Jsp000726.LowerIteration

@[expose] public section

namespace Jsp000726

/-- The §3 moment bound for the early subset-sum counts, normalized also at a zero-length prefix. -/
def EarlyCountMoment (a : ℕ → ℕ) (c w : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
    (max 1 (prefixWeight a n : ℝ)) ^ ((1 + w) / 2) ≤
      K * (allCounts a n : ℝ) * ((n : ℝ) + 1) ^ (c * ((1 - w) / 2))

def NextPrefixBound (a : ℕ → ℕ) (c : ℝ) : Prop :=
  ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ,
    (prefixWeight a (n + 1) : ℝ) ≤ D * max (max 1 (prefixWeight a n : ℝ)) (((n : ℝ) + 1) ^ c)

def PrefixWeightCap (a : ℕ → ℕ) (b : ℝ) : Prop :=
  ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ,
    (prefixWeight a (n + 1) : ℝ) ≤ D * ((n : ℝ) + 1) ^ b

private noncomputable def countGain (c U w : ℝ) : ℝ :=
  ((1 + w) / 2) / (1 + c * ((1 - w) / 2) / U)

private theorem continuousAt_countGain {c U w : ℝ} (hc : 0 < c) (hU : 0 < U) (hw : w ≤ 1) :
    ContinuousAt (countGain c U) w := by
  have hv : 0 ≤ c * ((1 - w) / 2) / U := by
    exact div_nonneg (mul_nonneg hc.le (by linarith)) hU.le
  have hden : 1 + c * ((1 - w) / 2) / U ≠ 0 := by linarith
  exact (((continuous_const.add continuous_id).div_const _).continuousAt).div
    ((continuous_const.add ((continuous_const.mul ((continuous_const.sub continuous_id).div_const _)).div_const _)).continuousAt)
    hden

private theorem lt_countGain {c U w : ℝ} (hc : 0 < c) (hU : 0 < U) (hw : w < 1) (hwu : w < U / c) :
    w < countGain c U w := by
  have he := (lt_div_iff₀ hc).mp hwu
  have hpos : 0 < 1 - c * w / U := by
    have hh : c * w / U < 1 := by
      apply (div_lt_iff₀ hU).2
      rw [one_mul, mul_comm]
      exact he
    linarith
  have hden : 0 < 1 + c * ((1 - w) / 2) / U := by
    have hh := div_nonneg (mul_nonneg hc.le (show 0 ≤ (1 - w) / 2 by linarith)) hU.le
    linarith
  unfold countGain
  apply (lt_div_iff₀ hden).2
  have hprod : 0 < (1 - w) / 2 * (1 - c * w / U) := mul_pos (by linarith) hpos
  have halg : (1 + w) / 2 - w * (1 + c * ((1 - w) / 2) / U) = (1 - w) / 2 * (1 - c * w / U) := by ring
  linarith

/-- Iterating the improved early total-count exponent gives every exponent below `(u+1)/c`. -/
theorem early_allCounts_of_uniform_moment {a : ℕ → ℕ} (ha : Admissible a) (hpos : ∀ n, 0 < a n)
    {u c b : ℝ} (hu : 0 < u) (hc : 0 < c) (huc : u + 1 ≤ c) (hb : c < b)
    (hW : PrefixPower (middleLayer a) u) (hcap : PrefixWeightCap a b) (hnext : NextPrefixBound a c)
    (hmoment : ∀ w : ℝ, 0 ≤ w → w < 1 → EarlyPower a (allCounts a) w → EarlyCountMoment a c w)
    {v : ℝ} (hv : v < (u + 1) / c) : EarlyPower a (allCounts a) v := by
  let U := u + 1
  have hU : 0 < U := by dsimp [U]; linarith
  have hZ := prefixPower_allCounts_of_middleLayer ha hu.le hW
  have hstart : EarlyPower a (allCounts a) (U / b) := earlyPower_of_prefixPower hpos (hc.trans hb) hU hZ hcap
  have h_end : U / c ≤ 1 := (div_le_iff₀ hc).2 (by simpa [U] using huc)
  apply all_below_of_continuous_gain hstart (earlyPower_antitone a (allCounts a))
    (f := countGain c U) _ _ _ v hv
  · intro w hw
    exact continuousAt_countGain hc hU (hw.2.trans_le h_end).le
  · intro w hw
    exact lt_countGain hc hU (hw.2.trans_le h_end) hw.2
  · intro w hw hwF
    have hw₀ := (div_nonneg hU.le (hc.trans hb).le).trans hw.1
    have hw₁ := hw.2.trans_le h_end
    have hM := hmoment w hw₀ hw₁ hwF
    have hα : 0 < (1 + w) / 2 := by linarith
    have hr := mul_nonneg hc.le (show 0 ≤ (1 - w) / 2 by linarith)
    have hstep := earlyPower_of_two_branches hpos hc hα hU hr hZ hnext hM
    simpa only [min_comm, countGain] using hstep

private theorem exists_largest_layer_gain {u c v : ℝ} (hu : 0 < u) (hc : 0 < c)
    (huc : u + 1 ≤ c) (hv₀ : 0 < v) (hv : v < u / c) :
    ∃ w : ℝ, 0 ≤ w ∧ w < (u + 1) / c ∧
      v < ((1 + w) / 2) / (1 + (1 + c * ((1 - w) / 2)) / u) := by
  let U := u + 1
  let cut := (v * (2 * U + c) - u) / (u + v * c)
  have hU : 0 < U := by dsimp [U]; linarith
  have hd : 0 < u + v * c := add_pos hu (mul_pos hv₀ hc)
  have hcut : cut < U / c := by
    dsimp [cut]
    apply (div_lt_iff₀ hd).2
    have hv' := (lt_div_iff₀ hc).mp hv
    have halg : U / c * (u + v * c) - (v * (2 * U + c) - u) =
        ((U + c) / c) * (u - v * c) := by field_simp; ring
    have hh := mul_pos (div_pos (add_pos hU hc) hc) (sub_pos.mpr hv')
    linarith
  have hmax : max 0 cut < U / c := (max_lt_iff).2 ⟨div_pos hU hc, hcut⟩
  let w := (max 0 cut + U / c) / 2
  have hw₀ : 0 ≤ w := div_nonneg (add_nonneg (le_max_left _ _) (div_nonneg hU.le hc.le)) (by norm_num)
  have hwU : w < U / c := by dsimp [w]; linarith
  have hcutw : cut < w := by
    have hleft := le_max_right (0 : ℝ) cut
    dsimp [w]
    linarith
  have hend : U / c ≤ (1 : ℝ) := (div_le_iff₀ hc).2 (by rw [one_mul]; exact huc)
  have hw₁ := hwU.trans_le hend
  have hr : 0 ≤ (1 + c * ((1 - w) / 2)) / u :=
    div_nonneg (add_nonneg zero_le_one (mul_nonneg hc.le (by linarith))) hu.le
  refine ⟨w, hw₀, hwU, (lt_div_iff₀ (by linarith : 0 < 1 + (1 + c * ((1 - w) / 2)) / u)).2 ?_⟩
  have hs := (div_lt_iff₀ hd).mp hcutw
  have halg : 2 * u * (((1 + w) / 2) - v * (1 + (1 + c * ((1 - w) / 2)) / u)) =
      w * (u + v * c) - (v * (2 * U + c) - u) := by
    dsimp [U]
    field_simp
    ring
  have hh : 0 < 2 * u * (((1 + w) / 2) - v * (1 + (1 + c * ((1 - w) / 2)) / u)) := by
    rw [halg]
    simpa only [mul_comm] using sub_pos.mpr hs
  have hp := pos_of_mul_pos_right hh (by positivity : 0 ≤ (2 : ℝ) * u)
  linarith

/-- The early-layer conclusion of manuscript Lemma 3.1, given the uniform moment input. -/
theorem early_largestLayer_of_uniform_moment {a : ℕ → ℕ} (ha : Admissible a) (hpos : ∀ n, 0 < a n)
    {u c b : ℝ} (hu : 0 < u) (hc : 0 < c) (huc : u + 1 ≤ c) (hb : c < b)
    (hW : PrefixPower (middleLayer a) u) (hcap : PrefixWeightCap a b) (hnext : NextPrefixBound a c)
    (hmoment : ∀ w : ℝ, 0 ≤ w → w < 1 → EarlyPower a (allCounts a) w → EarlyCountMoment a c w)
    {v : ℝ} (hv₀ : 0 < v) (hv : v < u / c) : EarlyPower a (largestLayer a) v := by
  obtain ⟨w, hw₀, hw, hgain⟩ := exists_largest_layer_gain hu hc huc hv₀ hv
  have hend : (u + 1) / c ≤ (1 : ℝ) := (div_le_iff₀ hc).2 (by rw [one_mul]; exact huc)
  have hw₁ := hw.trans_le hend
  have hZ := early_allCounts_of_uniform_moment ha hpos hu hc huc hb hW hcap hnext hmoment hw
  obtain ⟨K, hK, hM⟩ := hmoment w hw₀ hw₁ hZ
  have hF := prefixPower_largestLayer_of_middleLayer hW
  have hMF : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (max 1 (prefixWeight a n : ℝ)) ^ ((1 + w) / 2) ≤
      C * (largestLayer a n : ℝ) * ((n : ℝ) + 1) ^ (1 + c * ((1 - w) / 2)) := by
    refine ⟨K, hK, fun n => ?_⟩
    let p : ℝ := (n : ℝ) + 1
    have hp : 0 < p := by dsimp [p]; positivity
    have hh : (allCounts a n : ℝ) ≤ p * (largestLayer a n : ℝ) := by
      dsimp [p]
      exact_mod_cast allCounts_le_mul_largestLayer ha n
    calc
      _ ≤ K * (allCounts a n : ℝ) * p ^ (c * ((1 - w) / 2)) := hM n
      _ ≤ K * (p * (largestLayer a n : ℝ)) * p ^ (c * ((1 - w) / 2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hK.le) (Real.rpow_nonneg hp.le _)
      _ = _ := by
        change _ = K * (largestLayer a n : ℝ) * p ^ (1 + c * ((1 - w) / 2))
        rw [Real.rpow_add hp, Real.rpow_one]
        ring
  have hα : 0 < (1 + w) / 2 := by linarith
  have hr : 0 ≤ 1 + c * ((1 - w) / 2) := add_nonneg zero_le_one (mul_nonneg hc.le (by linarith))
  have hnew := earlyPower_of_two_branches hpos hc hα hu hr hF hnext hMF
  exact earlyPower_antitone a (largestLayer a) (le_min hgain.le hv.le) hnew

end Jsp000726
