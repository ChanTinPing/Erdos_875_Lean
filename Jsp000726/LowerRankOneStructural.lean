module

public import Jsp000726.LowerStructuralBridge
public import Jsp000726.LowerRankOneGain
public import Jsp000726.LowerPairSupport
public import Jsp000726.LowerEarly
public import Jsp000726.LowerGainChoice
public import Jsp000726.LowerAsymptoticsRanks
public import Mathlib.Algebra.BigOperators.Fin

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726

open Finset PublicStructure

private theorem progressionInLayer_of_positive_integer_affine
    {a : ℕ → ℕ} {t : Finset ℕ} {q l : ℕ} {B d : ℤ} (hd : 0 < d)
    (hmem : ∀ j : ℕ, j ≤ l → B + (j : ℤ) * d ∈ (sumLayer a t q).map Nat.castEmbedding) :
    ∃ b : ℕ, ProgressionInLayer a t q b d.natAbs (l + 1) := by
  obtain ⟨b, _, hbase⟩ := mem_map.mp (hmem 0 (Nat.zero_le _))
  have hbase' : (b : ℤ) = B := by simpa only [Nat.castEmbedding_apply, Nat.cast_zero,
    zero_mul, add_zero] using hbase
  have hg : (d.natAbs : ℤ) = d := Int.natAbs_of_nonneg hd.le
  refine ⟨b, ?_⟩
  intro j hj
  obtain ⟨x, hx, hxe⟩ := mem_map.mp (hmem j (by omega))
  have heq : x = b + d.natAbs * j := by
    have hcast : (x : ℤ) = ((b + d.natAbs * j : ℕ) : ℤ) := by
      rw [Nat.cast_add, Nat.cast_mul, hbase', hg]
      simpa only [Nat.castEmbedding_apply, mul_comm (j : ℤ) d] using hxe
    exact Int.ofNat_inj.mp hcast
  exact mem_sumLayer.mp (heq ▸ hx)

/-- A nonconstant integer affine progression represented in one natural sum layer
may be reflected to take a positive natural step. -/
theorem progressionInLayer_of_integer_affine_with_abs
    {a : ℕ → ℕ} {t : Finset ℕ} {q l : ℕ} {B d : ℤ} (hd : d ≠ 0)
    (hmem : ∀ j : ℕ, j ≤ l → B + (j : ℤ) * d ∈ (sumLayer a t q).map Nat.castEmbedding) :
    ∃ b : ℕ, ProgressionInLayer a t q b d.natAbs (l + 1) := by
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · rw [← Int.natAbs_neg d]
    apply progressionInLayer_of_positive_integer_affine (B := B + (l : ℤ) * d) (d := -d) (by omega)
    intro j hj
    have h := hmem (l - j) (Nat.sub_le _ _)
    have heq : B + ((l - j : ℕ) : ℤ) * d = B + (l : ℤ) * d + (j : ℤ) * -d := by
      rw [Int.ofNat_sub hj]
      ring
    rwa [heq] at h
  · exact progressionInLayer_of_positive_integer_affine hpos hmem

/-- An integer affine progression has a positive natural step after orientation. -/
theorem progressionInLayer_of_integer_affine
    {a : ℕ → ℕ} {t : Finset ℕ} {q l : ℕ} {B d : ℤ} (hd : d ≠ 0)
    (hmem : ∀ j : ℕ, j ≤ l → B + (j : ℤ) * d ∈ (sumLayer a t q).map Nat.castEmbedding) :
    ∃ b g : ℕ, 0 < g ∧ ProgressionInLayer a t q b g (l + 1) := by
  obtain ⟨b, hb⟩ := progressionInLayer_of_integer_affine_with_abs hd hmem
  exact ⟨b, d.natAbs, Int.natAbs_pos.mpr hd, hb⟩

private theorem singleRank_param_card (length : Fin 1 → ℕ) :
    Fintype.card ((i : Fin 1) → Fin (length i + 1)) = length 0 + 1 := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin, Fin.prod_univ_one]

/-- The rank-one alternative of the structural theorem is a genuine ordinary
progression of the same cardinality in the natural fixed-size sum layer. -/
theorem progressionInLayer_of_rank_one_gap
    {a : ℕ → ℕ} {t : Finset ℕ} {q : ℕ} {offset : ℤ} {P : IntegerGAP}
    (hr : P.rank = 1) (hProper : P.Proper) (hcard : 2 ≤ P.carrier.card)
    (hmem : ∀ x ∈ P.carrier, offset + x ∈ (sumLayer a t q).map Nat.castEmbedding) :
    ∃ b g : ℕ, 0 < g ∧ ProgressionInLayer a t q b g P.carrier.card := by
  obtain ⟨rank, base, step, length⟩ := P
  change rank = 1 at hr
  subst rank
  let P : IntegerGAP := ⟨1, base, step, length⟩
  change P.Proper at hProper
  change 2 ≤ P.carrier.card at hcard
  change ∀ x ∈ P.carrier, _ at hmem
  change ∃ b g : ℕ, 0 < g ∧ ProgressionInLayer a t q b g P.carrier.card
  let l := length 0
  have hL : P.carrier.card = l + 1 := by
    rw [IntegerGAP.carrier, card_image_of_injective _ hProper, card_univ]
    exact singleRank_param_card length
  let param (j : Fin (l + 1)) : P.Param :=
    fun i => Fin.cast (by rw [Fin.eq_zero i]) j
  have hparam (j : Fin (l + 1)) : P.eval (param j) = base + (j.val : ℤ) * step 0 := by
    change base + (∑ i : Fin 1, ((param j i).val : ℤ) * step i) =
      base + (j.val : ℤ) * step 0
    rw [Fin.sum_univ_one]
    rfl
  have hstep : step 0 ≠ 0 := by
    intro hz
    let j : Fin (l + 1) := ⟨1, by omega⟩
    have he := hProper (show P.eval (param 0) = P.eval (param j) by simp [hparam, hz])
    have hv := congrArg (fun x : P.Param => (x 0).val) he
    have hv' : (0 : ℕ) = 1 := by
      simpa only [param, Fin.val_cast, j, Fin.val_zero] using hv
    omega
  have hassoc (j : ℕ) : offset + (base + (j : ℤ) * step 0) =
      offset + base + (j : ℤ) * step 0 := (add_assoc _ _ _).symm
  rw [hL]
  apply progressionInLayer_of_integer_affine hstep
  intro j hj
  have hx : P.eval (param ⟨j, by omega⟩) ∈ P.carrier := mem_image_of_mem _ (mem_univ _)
  have ht := hmem _ hx
  rw [hparam, hassoc] at ht
  exact ht

/-- The rank-one case of the structural bootstrap, with all constants uniform in the
particular progression supplied at each sufficiently large index. -/
theorem eventually_rank_one_gap_layer_gain {a : ℕ → ℕ} (hmono : StrictMono a)
    (hpos : ∀ n, 0 < a n) (ha : Admissible a) {c u v w : ℝ}
    (hc : 0 < c) (hu : 0 < u) (huc : u + 1 ≤ c) (hv₀ : 0 < v) (hv : v < u / c)
    (hμ : 0 < gapMu c v) (hw₀ : 0 ≤ w) (hw : w ≤ gapRankOneGain c v)
    (hW : PrefixPower (middleLayer a) u)
    (hgap : ∀ᶠ n : ℕ in Filter.atTop, (gap a n : ℝ) ≤ ((n : ℝ) + 1) ^ c)
    {C : ℕ} (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in Filter.atTop, ∀ P : IntegerGAP, P.rank = 1 → P.Proper →
      (n / 16) ^ (P.rank + 1) ≤ C * P.carrier.card →
      (∀ x ∈ P.carrier,
        ((∑ i : Fin (n / 16), a (oppositeLow (n / 2) (n / 16) i) : ℕ) : ℤ) + x ∈
          (sumLayer a (oppositeSupport (n / 2) (n / 16)) (n / 16)).map Nat.castEmbedding) →
      K * ((n : ℝ) + 1) ^ w ≤ middleLayer a n := by
  have hW' := hW
  obtain ⟨E, hE, hW⟩ := hW
  obtain ⟨F, hF, hEarly⟩ := early_largestLayer_of_eventual_gaps hmono hpos ha hc hu huc
    hW' hgap hv₀ hv
  obtain ⟨G, hG, hterm⟩ := polynomialTermBound_of_eventual_gaps hmono.monotone hc.le hgap
  have hterm' : ∃ G : ℝ, 0 < G ∧ ∀ n : ℕ, (a n : ℝ) ≤ G * ((n : ℝ) + 1) ^ (c + 1) := by
    exact ⟨G, hG, fun n => by simpa only [Nat.cast_add, Nat.cast_one] using hterm n⟩
  have hprefix := prefixWeightCap_of_termCap (by linarith : 0 ≤ c + 1) hterm'
  obtain ⟨A, hA, hpref⟩ := prefixWeightCap_to_pointwise hprefix
  let D : ℝ := 1 / (1024 * (C : ℝ))
  have hD : 0 < D := by
    dsimp [D]
    exact one_div_pos.mpr (mul_pos (by norm_num) (Nat.cast_pos.mpr hC))
  have hadd : c + 1 + 1 = c + 2 := by ring
  have hpref' : ∀ n : ℕ, (prefixWeight a n : ℝ) ≤ A * (n : ℝ) ^ (c + 2) := by
    simpa only [hadd] using hpref
  obtain ⟨K, hK, hgain⟩ := rankOne_gain_from_early_layers hpos ha hA hD hE hF hu.le huc
    hv₀.le hv.le hμ hpref' hW hEarly
  have htwo : 0 < (2 : ℝ) ^ w := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨K / (2 : ℝ) ^ w, div_pos hK htwo, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (32 * (C + 1))] with n hn P hr hProp hcard hmem
  have hn0 : 0 < n := by omega
  let m := n / 16
  let q := n / 2
  have hcard' : m ^ 2 ≤ C * P.carrier.card := by simpa only [hr] using hcard
  have hm : C < m := by dsimp [m]; omega
  have hm2 : m ≤ m ^ 2 := by
    simpa only [mul_one, pow_two] using Nat.mul_le_mul_left m (show 1 ≤ m by omega)
  have hlen : 2 ≤ P.carrier.card := by
    by_contra! h
    have hd := (hm2.trans hcard').trans (Nat.mul_le_mul_left C (by omega : P.carrier.card ≤ 1))
    omega
  have hN : n ≤ 32 * m := by dsimp [m]; omega
  have hDlower : D * (n : ℝ) ^ (2 : ℝ) ≤ (P.carrier.card : ℝ) := by
    have hh : n ^ 2 ≤ 1024 * (C * P.carrier.card) := by
      calc
        n ^ 2 ≤ (32 * m) ^ 2 := Nat.pow_le_pow_left hN 2
        _ = 1024 * m ^ 2 := by rw [mul_pow]; norm_num
        _ ≤ _ := Nat.mul_le_mul_left _ hcard'
    have hcast : (n : ℝ) ^ (2 : ℕ) ≤ 1024 * ((C : ℝ) * (P.carrier.card : ℝ)) := by
      exact_mod_cast hh
    dsimp [D]
    rw [one_div, ← div_eq_inv_mul, div_le_iff₀ (by positivity),
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hcast
  obtain ⟨b, g, hg, hprog⟩ := progressionInLayer_of_rank_one_gap hr hProp hlen hmem
  have ht : oppositeSupport q m ⊆ range n := oppositeSupport_subset_range (by dsimp [q, m]; omega)
  have hd : Disjoint (range (n / 4)) (oppositeSupport q m) :=
    disjoint_range_oppositeSupport (by dsimp [q]; omega)
  have htcard : (oppositeSupport q m).card ≤ n / 4 := by
    rw [oppositeSupport_card]
    dsimp [m]
    omega
  have hf := hgain hn0 hg hlen ht hd htcard hprog hDlower
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have ha' : ((n : ℝ) + 1) ^ w ≤ (2 * (n : ℝ)) ^ w :=
    Real.rpow_le_rpow (by positivity) (by linarith) hw₀
  rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg n)] at ha'
  calc
    K / (2 : ℝ) ^ w * ((n : ℝ) + 1) ^ w ≤
      K / (2 : ℝ) ^ w * ((2 : ℝ) ^ w * (n : ℝ) ^ w) :=
      mul_le_mul_of_nonneg_left ha' (div_nonneg hK.le htwo.le)
    _ = K * (n : ℝ) ^ w := by field_simp
    _ ≤ K * (n : ℝ) ^ (gapRankOneGain c v) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 hw) hK.le
    _ ≤ middleLayer a n := hf

/-- The exact rank-one case in the opposite-pair structural bootstrap interface. -/
theorem oppositeRankGain_one_of_eventual_gaps {a : ℕ → ℕ} (hmono : StrictMono a)
    (hpos : ∀ i, 0 < a i) (ha : Admissible a) {c u v w : ℝ}
    (hc : 0 < c) (hu : 0 < u) (huc : u + 1 ≤ c) (hv₀ : 0 < v) (hv : v < u / c)
    (hμ : 0 < gapMu c v) (hw₀ : 0 ≤ w) (hw : w ≤ gapRankOneGain c v)
    (hW : PrefixPower (middleLayer a) u)
    (hgap : ∀ᶠ n : ℕ in Filter.atTop, (gap a n : ℝ) ≤ ((n : ℝ) + 1) ^ c)
    (C : ℕ) (hC : 0 < C) : OppositeRankGain a C 1 w := by
  obtain ⟨K, hK, h⟩ := eventually_rank_one_gap_layer_gain hmono hpos ha hc hu huc hv₀ hv hμ
    hw₀ hw hW hgap hC
  refine ⟨K, hK, h.mono ?_⟩
  intro n hn P hr hP
  obtain ⟨hproper, _, hcard, htranslation⟩ := hP
  exact hn P hr hproper hcard htranslation

/-- The chain-length bound (4.1) under the actual polynomial gap hypothesis. -/
theorem progression_length_bound_of_eventual_gaps {a : ℕ → ℕ} (hmono : StrictMono a)
    (hpos : ∀ i, 0 < a i) (ha : Admissible a) {c u v : ℝ}
    (hc : 0 < c) (hu : 0 < u) (huc : u + 1 ≤ c) (hv₀ : 0 < v) (hv : v < u / c)
    (hW : PrefixPower (middleLayer a) u)
    (hgap : ∀ᶠ n : ℕ in Filter.atTop, (gap a n : ℝ) ≤ ((n : ℝ) + 1) ^ c) :
    ∃ D : ℝ, 0 < D ∧ ∀ {n q b g L : ℕ}, 0 < g → 2 ≤ L → ∀ {t : Finset ℕ},
      t ⊆ range n → Disjoint (range (n / 4)) t → ProgressionInLayer a t q b g L →
      (L : ℝ) ≤ D * (g : ℝ) ^ gapMu c v := by
  obtain ⟨F, hF, hEarly⟩ :=
    early_largestLayer_of_eventual_gaps hmono hpos ha hc hu huc hW hgap hv₀ hv
  obtain ⟨E, hE, hW⟩ := hW
  obtain ⟨G, hG, hterm⟩ := polynomialTermBound_of_eventual_gaps hmono.monotone hc.le hgap
  have hterm' : ∃ G : ℝ, 0 < G ∧ ∀ n : ℕ, (a n : ℝ) ≤ G * ((n : ℝ) + 1) ^ (c + 1) := by
    exact ⟨G, hG, fun n => by simpa only [Nat.cast_add, Nat.cast_one] using hterm n⟩
  obtain ⟨A, hA, hpref⟩ := prefixWeightCap_to_pointwise
    (prefixWeightCap_of_termCap (by linarith : 0 ≤ c + 1) hterm')
  have hadd : c + 1 + 1 = c + 2 := by ring
  have hpref' : ∀ n : ℕ, (prefixWeight a n : ℝ) ≤ A * (n : ℝ) ^ (c + 2) := by
    simpa only [hadd] using hpref
  exact progression_length_bound_from_early_layers hpos ha hA hE hF hu.le huc hv₀.le hv.le
    hpref' hW hEarly

end Jsp000726
