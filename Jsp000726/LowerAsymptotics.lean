module

public import Jsp000726.Basic
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Data.Nat.Log

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726

open Finset

/-- The square of the last term is controlled by the sum and the local gap cap.
Telescoping consecutive square differences avoids a cutoff or a rounding argument. -/
theorem sq_le_two_mul_sum_of_gap_cap {a : ℕ → ℕ} (ha : Monotone a)
    {D : ℝ} (hD : 0 ≤ D) (hzero : (a 0 : ℝ) ≤ D) :
    ∀ n : ℕ, (∀ i < n, (gap a i : ℝ) ≤ D) →
      (a n : ℝ) ^ 2 ≤ 2 * D * ∑ i ∈ range (n + 1), (a i : ℝ) := by
  intro n
  induction n with
  | zero =>
    intro _
    simp only [Nat.zero_add, sum_range_one]
    nlinarith [mul_le_mul_of_nonneg_right hzero (Nat.cast_nonneg (a 0)),
      mul_nonneg hD (Nat.cast_nonneg (a 0))]
  | succ n ih =>
    intro hgap
    have hprev := ih fun i hi => hgap i (hi.trans (Nat.lt_succ_self _))
    have hinc : (a (n + 1) : ℝ) - (a n : ℝ) ≤ D := by
      have hh := hgap n (Nat.lt_succ_self n)
      unfold gap at hh
      simpa only [Nat.cast_sub (ha (Nat.le_succ _))] using hh
    have hmono : (a n : ℝ) ≤ a (n + 1) := Nat.cast_le.mpr (ha (Nat.le_succ _))
    have hsum : (a (n + 1) : ℝ) ^ 2 - (a n : ℝ) ^ 2 ≤ 2 * D * (a (n + 1) : ℝ) := by
      calc
        _ = ((a (n + 1) : ℝ) - a n) * ((a (n + 1) : ℝ) + a n) := by ring
        _ ≤ D * ((a (n + 1) : ℝ) + a n) :=
          mul_le_mul_of_nonneg_right hinc (by positivity)
        _ ≤ D * ((a (n + 1) : ℝ) + a (n + 1)) :=
          mul_le_mul_of_nonneg_left (add_le_add_right hmono _) hD
        _ = _ := by ring
    rw [sum_range_succ]
    linarith only [hprev, hsum, show 2 * D * ((∑ i ∈ range (n + 1), (a i : ℝ)) + a (n + 1)) =
        2 * D * (∑ i ∈ range (n + 1), (a i : ℝ)) + 2 * D * (a (n + 1) : ℝ) by ring]

/-- A polynomial bound on every gap gives the moment estimate used in §3. -/
theorem sq_le_mul_sum_rpow_of_gap_cap {a : ℕ → ℕ} (ha : Monotone a)
    {c C : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hgap : ∀ i, (gap a i : ℝ) ≤ C * ((i + 1 : ℕ) : ℝ) ^ c) (n : ℕ) :
    (a n : ℝ) ^ 2 ≤
      (2 * max C (a 0 : ℝ)) * (∑ i ∈ range (n + 1), (a i : ℝ)) *
        ((n + 1 : ℕ) : ℝ) ^ c := by
  let P := ((n + 1 : ℕ) : ℝ) ^ c
  have hP : 1 ≤ P := Real.one_le_rpow (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) hc
  have hmax : 0 ≤ max C (a 0 : ℝ) := hC.trans (le_max_left _ _)
  have hD : 0 ≤ max C (a 0 : ℝ) * P := mul_nonneg hmax (by linarith)
  have ha0 : (a 0 : ℝ) ≤ max C (a 0 : ℝ) * P := (le_max_right _ _).trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hP hmax)
  have hDcap : ∀ i < n, (gap a i : ℝ) ≤ max C (a 0 : ℝ) * P := by
    intro i hi
    refine (hgap i).trans (mul_le_mul (le_max_left _ _) ?_ (by positivity) hmax)
    apply Real.rpow_le_rpow (by positivity) _ hc
    exact_mod_cast Nat.succ_le_succ hi.le
  calc
    _ ≤ 2 * (max C (a 0 : ℝ) * P) * ∑ i ∈ range (n + 1), (a i : ℝ) :=
      sq_le_two_mul_sum_of_gap_cap ha hD ha0 n hDcap
    _ = _ := by dsimp [P]; ring

private theorem rpow_two_pow (j : ℕ) (u : ℝ) :
    ((2 : ℝ) ^ j) ^ u = ((2 : ℝ) ^ u) ^ j := by
  rw [← Real.rpow_natCast_mul (by norm_num) j u, mul_comm,
    Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]

/-- The discrete layer-cake estimate used in §3. A dyadic summation bounds the total
weight using only tail cardinalities. The constant depends solely on the tail exponent. -/
theorem sum_weights_le_of_tail_count {ι : Type*} (s : Finset ι) (a : ι → ℕ)
    {M : ℕ} (hM : 0 < M) (hle : ∀ i ∈ s, a i ≤ M)
    {w K : ℝ} (hw : w < 1) (hK : 0 ≤ K)
    (htail : ∀ H : ℕ, 0 < H →
      ((s.filter fun i => H ≤ a i).card : ℝ) * (H : ℝ) ^ w ≤ K) :
    (∑ i ∈ s, (a i : ℝ)) ≤
      (2 * (2 : ℝ) ^ (1 - w) / ((2 : ℝ) ^ (1 - w) - 1)) *
        K * (M : ℝ) ^ (1 - w) := by
  let m := Nat.log 2 M
  let q := (2 : ℝ) ^ (1 - w)
  have hq : 1 < q := Real.one_lt_rpow (by norm_num) (sub_pos.mpr hw)
  let level (j : ℕ) : ℝ := (2 : ℝ) ^ j
  have hcover (i : ι) (hi : i ∈ s) :
      (a i : ℝ) ≤ 2 * ∑ j ∈ range (m + 1), (if (2 : ℕ) ^ j ≤ a i then level j else 0) := by
    by_cases hzero : a i = 0
    · rw [hzero, Nat.cast_zero]
      exact mul_nonneg (by norm_num) (sum_nonneg fun j hj => by
        split <;> positivity)
    · let j := Nat.log 2 (a i)
      have hj : j ∈ range (m + 1) := mem_range.mpr
        (Nat.lt_succ_of_le (Nat.log_mono_right (hle i hi)))
      have hpow : (2 : ℕ) ^ j ≤ a i := Nat.pow_log_le_self _ hzero
      have hplus : (a i : ℝ) ≤ 2 * level j := by
        have hlt := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (a i)).le
        change a i ≤ 2 ^ (j + 1) at hlt
        simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, pow_succ, mul_comm, level] using
          (Nat.cast_le.mpr hlt : (a i : ℝ) ≤ ((2 ^ (j + 1) : ℕ) : ℝ))
      refine hplus.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
      have hsingle := single_le_sum (f := fun k : ℕ =>
        if (2 : ℕ) ^ k ≤ a i then level k else 0)
        (fun k _ => by split <;> positivity) hj
      simpa only [ite_eq_left hpow] using hsingle
  have hswap :
      (∑ i ∈ s, 2 * ∑ j ∈ range (m + 1), (if (2 : ℕ) ^ j ≤ a i then level j else 0)) =
        2 * ∑ j ∈ range (m + 1), ((s.filter fun i => (2 : ℕ) ^ j ≤ a i).card : ℝ) * level j := by
    rw [← mul_sum, sum_comm]
    congr 1
    apply sum_congr rfl
    intro j hj
    rw [← sum_filter, sum_const, nsmul_eq_mul]
  have hterm (j : ℕ) :
      ((s.filter fun i => (2 : ℕ) ^ j ≤ a i).card : ℝ) * level j ≤ K * q ^ j := by
    have hbound := htail ((2 : ℕ) ^ j) (by positivity)
    have heq : level j = (((2 : ℕ) ^ j : ℕ) : ℝ) ^ w * q ^ j := by
      simp only [level, q, Nat.cast_pow, Nat.cast_ofNat]
      rw [← rpow_two_pow j (1 - w), ← Real.rpow_add (by positivity),
        show w + (1 - w) = 1 by ring, Real.rpow_one]
    rw [heq, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hbound (pow_nonneg (le_of_lt (lt_trans zero_lt_one hq)) _)
  have hMpow : q ^ m ≤ (M : ℝ) ^ (1 - w) := by
    rw [show q ^ m = ((2 : ℝ) ^ m) ^ (1 - w) from (rpow_two_pow _ _).symm]
    refine Real.rpow_le_rpow (by positivity) ?_ (sub_nonneg.mpr hw.le)
    exact_mod_cast Nat.pow_log_le_self 2 hM.ne'
  calc
    _ ≤ ∑ i ∈ s, 2 * ∑ j ∈ range (m + 1), (if (2 : ℕ) ^ j ≤ a i then level j else 0) :=
      sum_le_sum hcover
    _ = 2 * ∑ j ∈ range (m + 1), ((s.filter fun i => (2 : ℕ) ^ j ≤ a i).card : ℝ) * level j :=
      hswap
    _ ≤ 2 * ∑ j ∈ range (m + 1), K * q ^ j :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => hterm j) (by norm_num)
    _ = 2 * K * ((q ^ (m + 1) - 1) / (q - 1)) := by
      rw [← mul_sum, geom_sum_eq (ne_of_gt hq), mul_assoc]
    _ ≤ 2 * K * (q ^ (m + 1) / (q - 1)) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) (sub_pos.mpr hq).le)
        (mul_nonneg (by norm_num) hK)
    _ = (2 * q / (q - 1)) * K * q ^ m := by rw [pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hMpow (mul_nonneg
      (div_nonneg (mul_nonneg (by norm_num) (le_of_lt (lt_trans zero_lt_one hq)))
        (sub_nonneg.mpr hq.le)) hK)

/-- The weight estimate only needs the nontrivial tail bound above a fixed threshold;
the total cardinality bounds the finitely many smaller thresholds. -/
theorem sum_weights_le_of_large_tail_count {ι : Type*} (s : Finset ι) (a : ι → ℕ)
    {M H₀ : ℕ} (hM : 0 < M) (hle : ∀ i ∈ s, a i ≤ M)
    {w C Z : ℝ} (hw : 0 ≤ w) (hw' : w < 1) (hC : 0 ≤ C)
    (hsize : (s.card : ℝ) ≤ Z)
    (htail : ∀ H : ℕ, 0 < H → H₀ ≤ H →
      ((s.filter fun i => H ≤ a i).card : ℝ) * (H : ℝ) ^ w ≤ C * Z) :
    (∑ i ∈ s, (a i : ℝ)) ≤
      (2 * (2 : ℝ) ^ (1 - w) / ((2 : ℝ) ^ (1 - w) - 1) * max C ((H₀ : ℝ) ^ w)) *
        Z * (M : ℝ) ^ (1 - w) := by
  have hZ : 0 ≤ Z := (Nat.cast_nonneg _).trans hsize
  let D := max C ((H₀ : ℝ) ^ w)
  have hD : 0 ≤ D := hC.trans (le_max_left _ _)
  have hall (H : ℕ) (hH : 0 < H) :
      ((s.filter fun i => H ≤ a i).card : ℝ) * (H : ℝ) ^ w ≤ D * Z := by
    by_cases hh : H₀ ≤ H
    · exact (htail H hH hh).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hZ)
    · have hcount : ((s.filter fun i => H ≤ a i).card : ℝ) ≤ Z :=
        (Nat.cast_le.mpr (card_le_card (filter_subset _ _))).trans hsize
      have hrpow : (H : ℝ) ^ w ≤ (H₀ : ℝ) ^ w :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr (le_of_lt (not_le.mp hh))) hw
      calc
        _ ≤ Z * (H₀ : ℝ) ^ w := mul_le_mul hcount hrpow (by positivity) hZ
        _ ≤ Z * D := mul_le_mul_of_nonneg_left (le_max_right _ _) hZ
        _ = _ := mul_comm _ _
  simpa only [D, ← mul_assoc] using
    sum_weights_le_of_tail_count s a hM hle hw' (mul_nonneg hD hZ) hall

end Jsp000726
