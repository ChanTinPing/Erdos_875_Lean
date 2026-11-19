module

public import Jsp000726.LowerRankOnePowers
public import Jsp000726.LowerRankOnePrefix

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726

open Finset

private theorem rankOne_step_upper {N g L V p C D : ℝ}
    (hN : 0 < N) (hg : 0 ≤ g) (hD : 0 < D)
    (hlen : D * N ^ (2 : ℝ) ≤ L) (hspan : g * L ≤ 2 * V)
    (hV : V ≤ C * N ^ (p + 2)) :
    g ≤ (2 * C / D) * N ^ p := by
  have h := ((mul_le_mul_of_nonneg_left hlen hg).trans hspan).trans
    (mul_le_mul_of_nonneg_left hV (by norm_num : (0 : ℝ) ≤ 2))
  rw [Real.rpow_add hN] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ hD]
  apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hN (2 : ℝ))).mp
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

private theorem largestLayer_pos_for_gain (a : ℕ → ℕ) (n : ℕ) :
    1 ≤ largestLayer a n := by
  have h : 0 ∈ sumLayer a (range n) 0 := mem_sumLayer.mpr ⟨∅, empty_subset _, rfl, by simp⟩
  exact (card_pos.mpr ⟨0, h⟩).trans_le (card_sumLayer_le_largestLayer _ (Nat.zero_le _))

private theorem gain_of_uncapped_early_prefix {a : ℕ → ℕ} {v D : ℝ}
    (hv : 0 ≤ v) (hD : 0 < D)
    (hF : ∀ x : ℕ, 1 ≤ x → D * (x : ℝ) ^ v ≤ largestLayer a (prefixAt a x)) :
    ∀ g : ℕ, (min ((4 : ℝ) ^ v)⁻¹ (D * (1 / 8 : ℝ) ^ v)) * (g : ℝ) ^ v ≤
      largestLayer a (prefixAt a (g / 4)) := by
  intro g
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg _
  by_cases hg : 4 ≤ g
  · have hx : 1 ≤ g / 4 := by omega
    have h8 : g ≤ 8 * (g / 4) := by omega
    have h8' : (g : ℝ) ≤ 8 * (↑(g / 4 : ℕ) : ℝ) := by exact_mod_cast h8
    have hbase : (1 / 8 : ℝ) * g ≤ (g / 4 : ℕ) := by linarith
    have hp := Real.rpow_le_rpow (by positivity : 0 ≤ (1 / 8 : ℝ) * g) hbase hv
    rw [Real.mul_rpow (by norm_num) hg0] at hp
    have hscaled : (D * (1 / 8 : ℝ) ^ v) * (g : ℝ) ^ v ≤ D * ((g / 4 : ℕ) : ℝ) ^ v := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hD.le
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg hg0 _)).trans
      (hscaled.trans (hF _ hx))
  · have hbound : (g : ℝ) ≤ 4 := by exact_mod_cast Nat.le_of_lt (Nat.lt_of_not_ge hg)
    have hp := Real.rpow_le_rpow hg0 hbound hv
    have h₁ : (1 : ℝ) ≤ largestLayer a (prefixAt a (g / 4)) := by
      exact_mod_cast largestLayer_pos_for_gain a (prefixAt a (g / 4))
    have hpow : 0 < (4 : ℝ) ^ v := Real.rpow_pos_of_pos (by norm_num) _
    refine (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg hg0 _)).trans
      ((mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hpow.le)).trans ?_)
    simpa only [inv_mul_cancel₀ hpow.ne'] using h₁

private theorem progression_packing_alternatives {a : ℕ → ℕ}
    (hpos : ∀ i, 0 < a i) (ha : Admissible a)
    {B u v C E F : ℝ} (hB : 0 < B) (hC : 0 < C) (hE : 0 < E) (hF : 0 < F)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hpref : ∀ j : ℕ, (prefixWeight a j : ℝ) ≤ C * (j : ℝ) ^ B)
    (hW : ∀ j : ℕ, E * ((j : ℝ) + 1) ^ u ≤ middleLayer a j)
    (hEarly : ∀ x : ℕ, 1 ≤ x → F * (x : ℝ) ^ v ≤ largestLayer a (prefixAt a x)) :
    ∃ A U Y : ℝ, 0 < A ∧ 0 < U ∧ 0 < Y ∧
      ∀ {n q b g L : ℕ}, 0 < g → 2 ≤ L → ∀ {t : Finset ℕ},
        t ⊆ range n → Disjoint (range (n / 4)) t → ProgressionInLayer a t q b g L →
        ∃ m j : ℕ, m ≤ n / 4 ∧ j ≤ m ∧ prefixWeight a j < g ∧
          A * ((g : ℝ) * (L : ℝ)) ^ (1 / B) ≤ (m : ℝ) + 1 ∧
          ((U * (g : ℝ) ^ v ≤ largestLayer a j ∧
              (U / 2) * ((m : ℝ) + 1) * (g : ℝ) ^ v ≤ g) ∨
            (E * (((m : ℝ) + 1) / 4) ^ u ≤ largestLayer a j ∧
              (Y / 2) * ((m : ℝ) + 1) ^ (u + 1) ≤ g)) := by
  let A := (1 / 2 : ℝ) ^ (1 / B) / (4 * C ^ (1 / B))
  have hA : 0 < A := by dsimp [A]; positivity
  let U := min ((4 : ℝ) ^ v)⁻¹ (F * (1 / 8 : ℝ) ^ v)
  have hU : 0 < U := by dsimp [U]; positivity
  let Y := E * (1 / 4 : ℝ) ^ u
  have hY : 0 < Y := by dsimp [Y]; positivity
  refine ⟨A, U, Y, hA, hU, hY, ?_⟩
  intro n q b g L hg hL t ht hdis hprog
  let V := g * (L - 1)
  have hspan : V ≤ prefixWeight a n :=
    (progression_span_le_weight (by omega) hprog).trans (sum_le_sum_of_subset ht)
  have htotal : (V : ℝ) ≤ C * (n : ℝ) ^ B :=
    (Nat.cast_le.mpr hspan).trans (hpref _)
  have hhalf : (g : ℝ) * (L : ℝ) ≤ 2 * (V : ℝ) := by
    have h : g * L ≤ 2 * V := by
      dsimp [V]
      rw [Nat.mul_left_comm 2]
      exact Nat.mul_le_mul_left _ (by omega)
    exact_mod_cast h
  obtain ⟨m, hm, hmV, hmroot⟩ := exists_protected_prefix_of_span hpos hC hB hpref htotal
  have hmlo : A * ((g : ℝ) * (L : ℝ)) ^ (1 / B) ≤ (m : ℝ) + 1 := by
    have hl : (1 / 2 : ℝ) * ((g : ℝ) * (L : ℝ)) ≤ V := by linarith
    have h := Real.rpow_le_rpow (by positivity : 0 ≤ (1 / 2 : ℝ) * ((g : ℝ) * (L : ℝ)))
      hl (one_div_nonneg.mpr hB.le)
    rw [Real.mul_rpow (by norm_num) (by positivity)] at h
    calc
      A * ((g : ℝ) * (L : ℝ)) ^ (1 / B) =
          ((1 / 2 : ℝ) ^ (1 / B) * ((g : ℝ) * (L : ℝ)) ^ (1 / B)) / (4 * C ^ (1 / B)) := by
        dsimp [A]
        rw [div_mul_eq_mul_div]
      _ ≤ (V : ℝ) ^ (1 / B) / (4 * C ^ (1 / B)) := div_le_div_of_nonneg_right h (by positivity)
      _ ≤ (m : ℝ) + 1 := hmroot
  let j := min (prefixAt a (g / 4)) (m / 4)
  have hjm : j ≤ m := (min_le_right _ _).trans (Nat.div_le_self _ _)
  have hsmall : prefixWeight a j < g := by
    exact ((prefixWeight_mono a (min_le_left _ _)).trans (prefixWeight_at_le _ _)).trans_lt
      (Nat.div_lt_self hg (by decide))
  have hpacking : largestLayer a j * (m - j + 1) ≤ g :=
    largestLayer_mul_le_of_protected_prefix ha hjm (hdis.mono_left (range_mono hm))
      hg (by omega) hprog hmV hsmall
  have hpack : (largestLayer a j : ℝ) * ((m - j + 1 : ℕ) : ℝ) ≤ g := by
    exact_mod_cast hpacking
  have hpad : ((m : ℝ) + 1) / 2 ≤ ((m - j + 1 : ℕ) : ℝ) := by
    have hj : j ≤ m / 4 := min_le_right _ _
    have h : m + 1 ≤ 2 * (m - j + 1) := by omega
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    rw [mul_comm]
    exact_mod_cast h
  refine ⟨m, j, hm, hjm, hsmall, hmlo, ?_⟩
  have hm0 : 0 ≤ (m : ℝ) + 1 := by positivity
  by_cases hcap : prefixAt a (g / 4) ≤ m / 4
  · have hj : j = prefixAt a (g / 4) := min_eq_left hcap
    have he : U * (g : ℝ) ^ v ≤ largestLayer a j := by
      rw [hj]
      exact gain_of_uncapped_early_prefix hv hF hEarly g
    refine Or.inl ⟨he, ?_⟩
    have h := (mul_le_mul he hpad (div_nonneg hm0 (by norm_num)) (Nat.cast_nonneg _)).trans hpack
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h
  · have hj : j = m / 4 := min_eq_right (Nat.le_of_not_ge hcap)
    have hfloor : ((m : ℝ) + 1) / 4 ≤ (j : ℝ) + 1 := by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
      have h : m + 1 ≤ (j + 1) * 4 := by rw [hj]; omega
      exact_mod_cast h
    have he : E * (((m : ℝ) + 1) / 4) ^ u ≤ largestLayer a j :=
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hfloor hu) hE.le).trans
        ((hW j).trans (Nat.cast_le.mpr (middleLayer_le_largestLayer a j)))
    refine Or.inr ⟨he, ?_⟩
    have hh := (mul_le_mul he hpad (div_nonneg hm0 (by norm_num)) (Nat.cast_nonneg _)).trans hpack
    rw [Real.rpow_add (by positivity : 0 < (m : ℝ) + 1), Real.rpow_one]
    have hYeq : E * (((m : ℝ) + 1) / 4) ^ u = Y * ((m : ℝ) + 1) ^ u := by
      rw [div_eq_inv_mul, Real.mul_rpow (by positivity) hm0]
      simp only [Y, one_div, mul_assoc]
    rw [hYeq] at hh
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hh

/-- Residue packing supplies (4.1) uniformly over ordinary progressions in the paired
support. In particular the bound applies to a single chain of a rank-two box. -/
theorem progression_length_bound_from_early_layers {a : ℕ → ℕ} (hpos : ∀ i, 0 < a i)
    (ha : Admissible a) {p u v C E F : ℝ} (hC : 0 < C) (hE : 0 < E) (hF : 0 < F)
    (hu : 0 ≤ u) (hup : u + 1 ≤ p) (hv : 0 ≤ v) (hvp : v ≤ u / p)
    (hpref : ∀ j : ℕ, (prefixWeight a j : ℝ) ≤ C * (j : ℝ) ^ (p + 2))
    (hW : ∀ j : ℕ, E * ((j : ℝ) + 1) ^ u ≤ middleLayer a j)
    (hEarly : ∀ x : ℕ, 1 ≤ x → F * (x : ℝ) ^ v ≤ largestLayer a (prefixAt a x)) :
    ∃ D : ℝ, 0 < D ∧ ∀ {n q b g L : ℕ}, 0 < g → 2 ≤ L → ∀ {t : Finset ℕ},
      t ⊆ range n → Disjoint (range (n / 4)) t → ProgressionInLayer a t q b g L →
      (L : ℝ) ≤ D * (g : ℝ) ^ (p + 1 - (p + 2) * v) := by
  let B := p + 2
  have hB : 0 < B := by dsimp [B]; linarith
  obtain ⟨A, U, Y, hA, hU, hY, hpack⟩ := progression_packing_alternatives hpos ha
    hB hC hE hF hu hv hpref hW hEarly
  let D := max (((U / 2)⁻¹ / A) ^ B) ((((Y / 2)⁻¹) ^ (1 / (u + 1)) / A) ^ B)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro n q b g L hg hL t ht hd hprog
  obtain ⟨m, _, _, _, _, hlo, hb⟩ := hpack hg hL ht hd hprog
  have hb' := hb.imp And.right And.right
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have h := progression_length_le_rpow_of_packing_cases hg1 (Nat.cast_nonneg _) hB hu hup hvp
    hA (by positivity) (by positivity) hlo hb'
  have hE : B - 1 - B * v = p + 1 - (p + 2) * v := by dsimp [B]; ring
  rw [hE] at h
  exact h

/-- Uniform quantitative rank-one gain, assuming the early-layer estimate of
Lemma 3.1 and one progression with a quadratic length lower bound. Here the
prefix weight cap has exponent `p + 2`, so the progression step has exponent `p`. -/
theorem rankOne_gain_from_early_layers {a : ℕ → ℕ} (hpos : ∀ i, 0 < a i) (ha : Admissible a)
    {p u v C D E F : ℝ} (hC : 0 < C) (hD : 0 < D) (hE : 0 < E) (hF : 0 < F)
    (hu : 0 ≤ u) (hup : u + 1 ≤ p) (hv : 0 ≤ v) (hvp : v ≤ u / p)
    (hμ : 0 < p + 1 - (p + 2) * v)
    (hpref : ∀ j : ℕ, (prefixWeight a j : ℝ) ≤ C * (j : ℝ) ^ (p + 2))
    (hW : ∀ j : ℕ, E * ((j : ℝ) + 1) ^ u ≤ middleLayer a j)
    (hEarly : ∀ x : ℕ, 1 ≤ x → F * (x : ℝ) ^ v ≤ largestLayer a (prefixAt a x)) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {n q b g L : ℕ} (_hn : 0 < n) (_hg : 0 < g) (_hL : 2 ≤ L) {t : Finset ℕ},
        t ⊆ range n → Disjoint (range (n / 4)) t → t.card ≤ n / 4 →
        ProgressionInLayer a t q b g L → D * (n : ℝ) ^ (2 : ℝ) ≤ L →
          K * (n : ℝ) ^ (2 + 2 * v / (p + 1 - (p + 2) * v)) ≤ middleLayer a n := by
  have hp : 0 < p := by linarith
  let B := p + 2
  have hB : 0 < B := by dsimp [B]; positivity
  let μ := p + 1 - (p + 2) * v
  have hμ' : 0 < μ := hμ
  obtain ⟨A, U, Y, hA, hU, hY, hpacking⟩ := progression_packing_alternatives hpos ha
    hB hC hE hF hu hv hpref hW hEarly
  let CM := max (((U / 2)⁻¹ / A) ^ B) ((((Y / 2)⁻¹) ^ (1 / (u + 1)) / A) ^ B)
  have hCM : 0 < CM := by dsimp [CM]; positivity
  let I := A * (D / (2 * C / D) ^ (2 / p)) ^ (1 / B)
  have hI : 0 < I := by dsimp [I]; positivity
  let Z := min U (E * (I / 4) ^ u)
  have hZ : 0 < Z := by dsimp [Z]; positivity
  let K := Z * (D / CM) ^ (v / μ) * D
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro n q b g L hn hg hL t ht hdis htcard hprog hlen
  have hN' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hg' : 0 < (g : ℝ) := Nat.cast_pos.mpr hg
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  let V := g * (L - 1)
  have hspan : V ≤ prefixWeight a n :=
    (progression_span_le_weight (by omega) hprog).trans (sum_le_sum_of_subset ht)
  have htotal : (V : ℝ) ≤ C * (n : ℝ) ^ B :=
    (Nat.cast_le.mpr hspan).trans (hpref _)
  have hhalf : (g : ℝ) * (L : ℝ) ≤ 2 * (V : ℝ) := by
    have h : g * L ≤ 2 * V := by
      dsimp [V]
      rw [Nat.mul_left_comm 2]
      exact Nat.mul_le_mul_left _ (by omega)
    exact_mod_cast h
  have hstep := rankOne_step_upper hN' hg'.le hD hlen hhalf htotal
  obtain ⟨m, j, hm, hjm, hsmall, hmlo, hb⟩ := hpacking hg hL ht hdis hprog
  have hcount : (largestLayer a j : ℝ) * (L : ℝ) ≤ middleLayer a n := by
    exact_mod_cast largestLayer_mul_progression_le_middleLayer ht
      (hdis.mono_left (range_mono (hjm.trans hm))) (by omega) hg (by omega) hprog hsmall
  have hboth : ((U / 2) * ((m : ℝ) + 1) * (g : ℝ) ^ v ≤ g ∨
      (Y / 2) * ((m : ℝ) + 1) ^ (u + 1) ≤ g) ∧
      Z * (g : ℝ) ^ v ≤ largestLayer a j := by
    have hgPow := Real.rpow_nonneg hg'.le v
    rcases hb with ⟨he, hb⟩ | ⟨he, hb⟩
    · exact ⟨Or.inl hb, (mul_le_mul_of_nonneg_right (min_le_left _ _) hgPow).trans he⟩
    · have hmI : I * (g : ℝ) ^ (1 / p) ≤ (m : ℝ) + 1 :=
        rankOne_protected_prefix_lower hN' hg' hp (by positivity) hD hA hstep hlen hmlo
      have hf' := rankOne_capped_layer_lower hg1 hu hvp hI hE hmI he
      exact ⟨Or.inr hb, (mul_le_mul_of_nonneg_right (min_le_right _ _) hgPow).trans hf'⟩
  have hLupper : (L : ℝ) ≤ CM * (g : ℝ) ^ μ := by
    have h := progression_length_le_rpow_of_packing_cases hg1 (Nat.cast_nonneg _) hB
      hu hup hvp hA (by positivity) (by positivity) hmlo hboth.1
    have hμid : B - 1 - B * v = μ := by dsimp [B, μ]; ring
    simpa only [hμid] using h
  exact rankOne_layer_power_lower_bound hN' hg' hv hμ' hCM hD hZ hlen hLupper hboth.2 hcount

end Jsp000726
