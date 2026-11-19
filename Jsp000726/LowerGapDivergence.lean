module

public import Jsp000726.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.ModEq

@[expose] public section

namespace Jsp000726

open Finset

/-- A representation of a difference of two subset sums on a tail of a sequence. -/
private structure TailDifference (a : ℕ → ℕ) (d N : ℕ) where
  left : Finset ℕ
  right : Finset ℕ
  left_tail : ∀ i ∈ left, N ≤ i
  right_tail : ∀ i ∈ right, N ≤ i
  eq_add : (∑ i ∈ left, a i) = (∑ i ∈ right, a i) + d

private def TailDifference.signedCard {a : ℕ → ℕ} {d N : ℕ}
    (u : TailDifference a d N) : ℤ := (u.left.card : ℤ) - u.right.card

private theorem TailDifference.hasUpper {a : ℕ → ℕ} {d N : ℕ}
    (u : TailDifference a d N) :
    ∃ M, N ≤ M ∧ (∀ i ∈ u.left, i < M) ∧ ∀ i ∈ u.right, i < M := by
  refine ⟨max N ((u.left ∪ u.right).sup id + 1), le_max_left _ _, ?_, ?_⟩
  · intro i hi
    exact lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := id) (mem_union_left _ hi)))
      (le_max_right _ _)
  · intro i hi
    exact lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := id) (mem_union_right _ hi)))
      (le_max_right _ _)

private theorem disjoint_of_before {s t : Finset ℕ} {N : ℕ}
    (hs : ∀ i ∈ s, i < N) (ht : ∀ i ∈ t, N ≤ i) : Disjoint s t := by
  exact Finset.disjoint_left.mpr fun i hi hj => (not_lt_of_ge (ht i hj)) (hs i hi)

private theorem signedCard_eq {a : ℕ → ℕ} (ha : Admissible a) {d N M : ℕ}
    (u : TailDifference a d N) (v : TailDifference a d M)
    (hul : ∀ i ∈ u.left, i < M) (hur : ∀ i ∈ u.right, i < M) :
    u.signedCard = v.signedCard := by
  have hleft := disjoint_of_before hul v.right_tail
  have hright := disjoint_of_before hur v.left_tail
  have hs : (∑ i ∈ u.left ∪ v.right, a i) = ∑ i ∈ u.right ∪ v.left, a i := by
    rw [sum_union hleft, sum_union hright, u.eq_add, v.eq_add]
    omega
  have h := ha _ _ hs
  rw [card_union_of_disjoint hleft, card_union_of_disjoint hright] at h
  unfold TailDifference.signedCard
  omega

private theorem multiple_tail_difference {a : ℕ → ℕ} {d N₀ : ℕ} (ha : Admissible a)
    (hrep : ∀ N, Nonempty (TailDifference a d N)) (u : TailDifference a d N₀)
    {B : ℕ} (hul : ∀ i ∈ u.left, i < B) (hur : ∀ i ∈ u.right, i < B) :
    ∀ m N : ℕ, B ≤ N → ∃ v : TailDifference a (m * d) N,
      v.signedCard = (m : ℤ) * u.signedCard := by
  intro m
  induction m with
  | zero =>
      intro N _
      exact ⟨⟨∅, ∅, by simp, by simp, by simp⟩, by simp [TailDifference.signedCard]⟩
  | succ m ih =>
      intro N hBN
      obtain ⟨r⟩ := hrep N
      obtain ⟨M, hNM, hrl, hrr⟩ := r.hasUpper
      obtain ⟨v, hv⟩ := ih M (hBN.trans hNM)
      let l := r.left ∪ v.left
      let t := r.right ∪ v.right
      have hl := disjoint_of_before hrl v.left_tail
      have ht := disjoint_of_before hrr v.right_tail
      have heq : (∑ i ∈ l, a i) = (∑ i ∈ t, a i) + (m + 1) * d := by
        dsimp [l, t]
        rw [sum_union hl, sum_union ht, r.eq_add, v.eq_add, Nat.add_mul, Nat.one_mul]
        omega
      let w : TailDifference a ((m + 1) * d) N := ⟨l, t,
        fun i hi => (mem_union.mp hi).elim (r.left_tail i) (fun h => hNM.trans (v.left_tail i h)),
        fun i hi => (mem_union.mp hi).elim (r.right_tail i) (fun h => hNM.trans (v.right_tail i h)),
        heq⟩
      have hr := signedCard_eq ha u r
        (fun i hi => (hul i hi).trans_le hBN) (fun i hi => (hur i hi).trans_le hBN)
      refine ⟨w, ?_⟩
      have hw : w.signedCard = r.signedCard + v.signedCard := by
        simp only [TailDifference.signedCard, w, l, t, card_union_of_disjoint hl,
          card_union_of_disjoint ht, Nat.cast_add]
        omega
      rw [hw, ← hr, hv, Nat.cast_succ, add_mul, one_mul, add_comm]

private theorem nonempty_subset_sum_multiple (b : ℕ → ℕ) {d : ℕ} (hd : 0 < d) :
    ∃ s : Finset ℕ, s.Nonempty ∧ s ⊆ range d ∧ d ∣ ∑ i ∈ s, b i := by
  let P (j : ℕ) := ∑ i ∈ range j, b i
  have hcard : (range d).card < (range (d + 1)).card := by simp
  obtain ⟨i, hi, j, hj, hne, hmod⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hcard
    (f := fun l => P l % d) (fun l _ => mem_range.mpr (Nat.mod_lt _ hd))
  let x := min i j
  let y := max i j
  have hxy : x < y := by
    dsimp [x, y]
    rcases lt_or_gt_of_ne hne with h | h
    · rwa [min_eq_left h.le, max_eq_right h.le]
    · rwa [min_eq_right h.le, max_eq_left h.le]
  have hym : y ≤ d := by
    dsimp [y]
    have hi' := mem_range.mp hi
    have hj' := mem_range.mp hj
    omega
  have hxyMod : P x ≡ P y [MOD d] := by
    change P x % d = P y % d
    dsimp [x, y]
    rcases lt_or_gt_of_ne hne with h | h
    · simpa only [min_eq_left h.le, max_eq_right h.le] using hmod
    · simpa only [min_eq_right h.le, max_eq_left h.le] using hmod.symm
  have hsub : range x ⊆ range y := range_mono hxy.le
  have hadd : (∑ i ∈ range y \ range x, b i) + P x = P y := sum_sdiff hsub
  have hp : P x ≤ P y := by omega
  refine ⟨range y \ range x, ⟨x, mem_sdiff.mpr ⟨mem_range.mpr hxy, by simp⟩⟩, ?_, ?_⟩
  · intro k hk
    exact mem_range.mpr ((mem_range.mp (mem_sdiff.mp hk).1).trans_le hym)
  · have hv := (Nat.modEq_iff_dvd' hp).mp hxyMod
    have h := show P y - P x = ∑ i ∈ range y \ range x, b i by omega
    simpa only [h] using hv

/-- Every fixed positive difference is absent between subset sums of a sufficiently late tail. -/
theorem eventually_no_subset_sum_difference {a : ℕ → ℕ} (hmono : StrictMono a)
    (ha : Admissible a) {d : ℕ} (hd : 0 < d) :
    ∃ N : ℕ, ∀ U V : Finset ℕ, (∀ i ∈ U, N ≤ i) → (∀ i ∈ V, N ≤ i) →
      (∑ i ∈ U, a i) ≠ (∑ i ∈ V, a i) + d := by
  by_contra! hreps
  have hrep (N : ℕ) : Nonempty (TailDifference a d N) := by
    obtain ⟨U, V, hU, hV, heq⟩ := hreps N
    exact ⟨⟨U, V, hU, hV, heq⟩⟩
  obtain ⟨u⟩ := hrep 0
  obtain ⟨B, _, hul, hur⟩ := u.hasUpper
  let K := d * d + 1
  let shift : ℕ ↪ ℕ := ⟨fun i => K + i, fun _ _ h => Nat.add_left_cancel h⟩
  obtain ⟨s, hs, hsd, k, hmul⟩ := nonempty_subset_sum_multiple (a ∘ shift) hd
  let S := s.map shift
  have hSsum : (∑ i ∈ S, a i) = d * k := by simpa only [S, Finset.sum_map, Function.comp_apply] using hmul
  have hScard : S.card ≤ d := by
    simpa only [S, card_map, card_range] using card_le_card hsd
  have hScardPos : 0 < S.card := by simpa only [S, card_map] using (card_pos.mpr hs)
  have hindex (i : ℕ) : i ≤ a i := by
    induction i with
    | zero => exact Nat.zero_le _
    | succ i hi => exact Nat.succ_le_of_lt (hi.trans_lt (hmono (Nat.lt_succ_self i)))
  have hsumBig : d * d < ∑ i ∈ S, a i := by
    obtain ⟨i, hi⟩ := hs
    have hiS : shift i ∈ S := mem_map.mpr ⟨i, hi, rfl⟩
    have hle : a (shift i) ≤ ∑ j ∈ S, a j := single_le_sum (fun _ _ => Nat.zero_le _) hiS
    have hK : d * d < shift i := by change d * d < d * d + 1 + i; omega
    exact hK.trans_le ((hindex _).trans hle)
  have hk : d < k := by
    by_contra! hkd
    exact (not_lt_of_ge (Nat.mul_le_mul_left d hkd)) (hSsum ▸ hsumBig)
  let N := max B (K + d)
  obtain ⟨v, hv⟩ := multiple_tail_difference ha hrep u hul hur k N (le_max_left _ _)
  have hSBefore : ∀ i ∈ S, i < N := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := mem_map.mp hi
    have hjd := mem_range.mp (hsd hj)
    have hjK : shift j < K + d := Nat.add_lt_add_left hjd K
    exact hjK.trans_le (le_max_right _ _)
  have hdis := disjoint_of_before hSBefore v.right_tail
  have heq : (∑ i ∈ S ∪ v.right, a i) = ∑ i ∈ v.left, a i := by
    rw [sum_union hdis, hSsum, v.eq_add, Nat.mul_comm d k, add_comm]
  have hcards := ha _ _ heq
  rw [card_union_of_disjoint hdis] at hcards
  have hcardEq : (S.card : ℤ) = (k : ℤ) * u.signedCard := by
    rw [← hv]
    unfold TailDifference.signedCard
    omega
  have hne : ¬ (k : ℤ) ∣ (S.card : ℤ) := by
    intro hdiv
    have hdivNat : k ∣ S.card := Int.ofNat_dvd.mp hdiv
    exact (not_le_of_gt (hScard.trans_lt hk)) (Nat.le_of_dvd hScardPos hdivNat)
  exact hne ⟨u.signedCard, hcardEq⟩

/-- All fixed upper bounds on consecutive gaps fail eventually along an admissible sequence. -/
theorem gaps_eventually_gt {a : ℕ → ℕ} (hmono : StrictMono a) (ha : Admissible a) :
    ∀ D : ℕ, ∃ N : ℕ, ∀ n ≥ N, D < gap a n := by
  intro D
  induction D with
  | zero =>
      exact ⟨0, fun n _ => Nat.sub_pos_of_lt (hmono (Nat.lt_succ_self n))⟩
  | succ D ih =>
      obtain ⟨N₁, hN₁⟩ := ih
      obtain ⟨N₂, hN₂⟩ := eventually_no_subset_sum_difference hmono ha (Nat.zero_lt_succ D)
      refine ⟨max N₁ N₂, fun n hn => ?_⟩
      have hn₁ := (le_max_left N₁ N₂).trans hn
      have hn₂ := (le_max_right N₁ N₂).trans hn
      have hgt := hN₁ n hn₁
      by_contra! hle
      have heq : gap a n = D + 1 := by omega
      have hne := hN₂ {n + 1} {n} (by simpa using hn₂.trans (Nat.le_succ n)) (by simpa using hn₂)
      simp only [sum_singleton] at hne
      have hmono' := (hmono (Nat.lt_succ_self n)).le
      unfold gap at heq
      exact hne (by omega)

/-- No nonpositive exponent can bound all sufficiently late consecutive gaps. -/
theorem not_eventualGapExponent_of_nonpos {c : ℝ} (hc : c ≤ 0) :
    ¬ EventualGapExponent c := by
  rintro ⟨a, hmono, _, ha, hbound⟩
  obtain ⟨N₁, h₁⟩ := gaps_eventually_gt hmono ha 1
  obtain ⟨N₂, h₂⟩ := Filter.eventually_atTop.mp hbound
  let n := max N₁ N₂
  have hgt : (1 : ℝ) < gap a n := by exact_mod_cast h₁ n (le_max_left _ _)
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hp : ((n : ℝ) + 1) ^ c ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn hc
  exact (not_lt_of_ge ((h₂ n (le_max_right _ _)).trans hp)) hgt

end Jsp000726
