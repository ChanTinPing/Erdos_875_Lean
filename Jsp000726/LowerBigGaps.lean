module

public import Jsp000726.Basic
public import Jsp000726.LowerSyndetic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

namespace Jsp000726

open Finset

private def prefixSum (b : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ range n, b i

private def SubsetSum (b : ℕ → ℕ) (x : ℕ) : Prop :=
  ∃ U : Finset ℕ, (∑ i ∈ U, b i) = x

private theorem prefixSum_succ (b : ℕ → ℕ) (n : ℕ) :
    prefixSum b (n + 1) = prefixSum b n + b n := sum_range_succ b n

private theorem prefixSubsetSums_near (b : ℕ → ℕ) (P : ℕ)
    (hdef : ∀ n, b n ≤ prefixSum b n + P) :
    ∀ n t : ℕ, t ≤ prefixSum b n → ∃ U : Finset ℕ, U ⊆ range n ∧
      t ≤ (∑ i ∈ U, b i) ∧ (∑ i ∈ U, b i) ≤ t + P := by
  intro n
  induction n with
  | zero =>
      intro t ht
      have : t = 0 := by simpa [prefixSum] using ht
      subst t
      exact ⟨∅, by simp⟩
  | succ n ih =>
      intro t ht
      by_cases hold : t ≤ prefixSum b n
      · obtain ⟨U, hU, h₁, h₂⟩ := ih t hold
        exact ⟨U, hU.trans (range_mono (Nat.le_succ n)), h₁, h₂⟩
      · by_cases hb : t ≤ b n
        · refine ⟨{n}, singleton_subset_iff.mpr (mem_range.mpr (Nat.lt_succ_self n)), ?_, ?_⟩
          · simpa only [sum_singleton] using hb
          · rw [sum_singleton]
            have hd := hdef n
            omega
        · rw [prefixSum_succ] at ht
          obtain ⟨U, hU, h₁, h₂⟩ := ih (t - b n) (by omega)
          have hnU : n ∉ U := fun h => (Nat.lt_irrefl _) (mem_range.mp (hU h))
          refine ⟨insert n U, insert_subset (mem_range.mpr (Nat.lt_succ_self n))
            (hU.trans (range_mono (Nat.le_succ n))), ?_, ?_⟩
          · rw [sum_insert hnU]
            omega
          · rw [sum_insert hnU]
            omega

private theorem subsetSums_near (b : ℕ → ℕ) (P : ℕ) (hpos : ∀ i, 0 < b i)
    (hdef : ∀ n, b n ≤ prefixSum b n + P) (t : ℕ) :
    ∃ x, t ≤ x ∧ x ≤ t + P ∧ SubsetSum b x := by
  have hsum (n : ℕ) : n ≤ prefixSum b n := by
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
        rw [prefixSum_succ]
        have h := hpos n
        omega
  obtain ⟨U, _, h₁, h₂⟩ := prefixSubsetSums_near b P hdef t t (hsum t)
  exact ⟨_, h₁, h₂, ⟨U, rfl⟩⟩

private noncomputable def subsetSumCeiling {b : ℕ → ℕ} {P : ℕ}
    (h : ∀ t, ∃ x, t ≤ x ∧ x ≤ t + P ∧ SubsetSum b x) (t : ℕ) : ℕ := by
  classical
  exact if SubsetSum b t then t else (h t).choose

private theorem subsetSumCeiling_eq {b : ℕ → ℕ} {P : ℕ}
    (h : ∀ t, ∃ x, t ≤ x ∧ x ≤ t + P ∧ SubsetSum b x) {t : ℕ}
    (ht : SubsetSum b t) : subsetSumCeiling h t = t := by
  simp [subsetSumCeiling, ht]

private theorem subsetSumCeiling_spec {b : ℕ → ℕ} {P : ℕ}
    (h : ∀ t, ∃ x, t ≤ x ∧ x ≤ t + P ∧ SubsetSum b x) (t : ℕ) :
    t ≤ subsetSumCeiling h t ∧ subsetSumCeiling h t ≤ t + P ∧ SubsetSum b (subsetSumCeiling h t) := by
  by_cases ht : SubsetSum b t
  · rw [subsetSumCeiling_eq h ht]
    exact ⟨le_rfl, Nat.le_add_right _ _, ht⟩
  · simpa only [subsetSumCeiling, ite_eq_right ht] using (h t).choose_spec

private noncomputable def subsetSumCard (b : ℕ → ℕ) (t : ℕ) : ℕ := by
  classical
  exact if h : SubsetSum b t then h.choose.card else 0

private theorem subsetSumCard_eq {b : ℕ → ℕ} (hb : Admissible b) (U : Finset ℕ) {t : ℕ}
    (ht : (∑ i ∈ U, b i) = t) : subsetSumCard b t = U.card := by
  have h : SubsetSum b t := ⟨U, ht⟩
  simp only [subsetSumCard, dite_eq_left h]
  exact hb _ _ (h.choose_spec.trans ht.symm)

private theorem admissible_comp_embedding {a : ℕ → ℕ} (ha : Admissible a) (e : ℕ ↪ ℕ) :
    Admissible (fun i => a (e i)) := by
  intro U V heq
  have h : (∑ i ∈ U.map e, a i) = ∑ i ∈ V.map e, a i := by simpa only [sum_map] using heq
  simpa only [card_map] using ha _ _ h

private theorem weight_bound_card (b : ℕ → ℕ) (hb : ∀ i, i ≤ b i) (U : Finset ℕ) (K : ℕ) :
    K * U.card ≤ (∑ i ∈ U, b i) + K * K := by
  let small := U ∩ range K
  let large := U \ range K
  have hs : small.card ≤ K := by
    simpa only [card_range] using card_le_card (show small ⊆ range K from inter_subset_right)
  have hlarge : K * large.card ≤ ∑ i ∈ large, b i := by
    have hh : (∑ _i ∈ large, K) ≤ ∑ i ∈ large, b i := by
      refine sum_le_sum fun i hi => (Nat.le_of_not_gt fun h => ?_).trans (hb i)
      exact (mem_sdiff.mp hi).2 (mem_range.mpr h)
    rw [sum_const, nsmul_eq_mul] at hh
    rw [mul_comm]
    exact hh
  have hsmall : K * small.card ≤ K * K := Nat.mul_le_mul_left K hs
  have hsub : small ⊆ U := inter_subset_left
  have hsDiff : U \ small = large := by
    ext i
    by_cases hi : i ∈ U <;> simp [small, large, hi]
  have hcard := card_sdiff_add_card_eq_card hsub
  have hsum : (∑ i ∈ U \ small, b i) + (∑ i ∈ small, b i) = ∑ i ∈ U, b i := sum_sdiff hsub
  rw [hsDiff] at hcard hsum
  rw [← hcard, Nat.mul_add]
  omega

private def evenIndex : ℕ ↪ ℕ where
  toFun i := 2 * i
  inj' i j h := by dsimp at h; omega

private def oddIndex : ℕ ↪ ℕ where
  toFun i := 2 * i + 1
  inj' i j h := by dsimp at h; omega

private theorem disjoint_even_odd (U V : Finset ℕ) : Disjoint (U.map evenIndex) (V.map oddIndex) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, _, hi⟩ := mem_map.mp hx
  obtain ⟨j, _, hj⟩ := mem_map.mp hy
  have h : evenIndex i = oddIndex j := hi.trans hj.symm
  change 2 * i = 2 * j + 1 at h
  omega

private theorem seq_le_values {a : ℕ → ℕ} (ha : StrictMono a) (i : ℕ) : i ≤ a i := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i hi => exact Nat.succ_le_of_lt (hi.trans_lt (ha (Nat.lt_succ_self i)))

private theorem no_two_bounded_parity_deficits {a : ℕ → ℕ} (hmono : StrictMono a)
    (hpos : ∀ i, 0 < a i) (ha : Admissible a) {P Q : ℕ}
    (he : ∀ j, a (2 * j) ≤ prefixSum (fun i => a (2 * i)) j + P)
    (ho : ∀ j, a (2 * j + 1) ≤ prefixSum (fun i => a (2 * i + 1)) j + Q) : False := by
  let b (i : ℕ) := a (evenIndex i)
  let e (i : ℕ) := a (oddIndex i)
  have hb := admissible_comp_embedding ha evenIndex
  have he' := admissible_comp_embedding ha oddIndex
  have hx t := subsetSums_near b P (fun i => hpos (evenIndex i)) he t
  have hy t := subsetSums_near e Q (fun i => hpos (oddIndex i)) ho t
  let x (t : ℕ) := subsetSumCeiling hx t
  let y (t : ℕ) := subsetSumCeiling hy t
  let F (t : ℕ) : ℤ := subsetSumCard b (x t)
  let G (t : ℕ) : ℤ := subsetSumCard e (y t)
  have hX t := subsetSumCeiling_spec hx t
  have hY t := subsetSumCeiling_spec hy t
  have hF0 : F 0 = 0 := by
    have hzero : (∑ i ∈ (∅ : Finset ℕ), b i) = 0 := sum_empty
    dsimp [F, x]
    rw [subsetSumCeiling_eq hx ⟨∅, hzero⟩, subsetSumCard_eq hb ∅ hzero]
    rfl
  have hcross i j i' j' (h : x i + y j = x i' + y j') : F i + G j = F i' + G j' := by
    obtain ⟨U, hU⟩ := (hX i).2.2
    obtain ⟨V, hV⟩ := (hY j).2.2
    obtain ⟨U', hU'⟩ := (hX i').2.2
    obtain ⟨V', hV'⟩ := (hY j').2.2
    change (∑ i ∈ U, b i) = x i at hU
    change (∑ i ∈ V, e i) = y j at hV
    change (∑ i ∈ U', b i) = x i' at hU'
    change (∑ i ∈ V', e i) = y j' at hV'
    have hd := disjoint_even_odd U V
    have hd' := disjoint_even_odd U' V'
    have hs : (∑ i ∈ U.map evenIndex ∪ V.map oddIndex, a i) =
        ∑ i ∈ U'.map evenIndex ∪ V'.map oddIndex, a i := by
      rw [sum_union hd, sum_union hd']
      simp only [sum_map]
      change (∑ i ∈ U, b i) + (∑ i ∈ V, e i) = (∑ i ∈ U', b i) + (∑ i ∈ V', e i)
      rw [hU, hV, hU', hV']
      exact h
    have hc := ha _ _ hs
    rw [card_union_of_disjoint hd, card_union_of_disjoint hd'] at hc
    simp only [card_map] at hc
    rw [show F i = (U.card : ℤ) from congrArg Nat.cast (subsetSumCard_eq hb U hU),
      show F i' = (U'.card : ℤ) from congrArg Nat.cast (subsetSumCard_eq hb U' hU'),
      show G j = (V.card : ℤ) from congrArg Nat.cast (subsetSumCard_eq he' V hV),
      show G j' = (V'.card : ℤ) from congrArg Nat.cast (subsetSumCard_eq he' V' hV')]
    exact_mod_cast hc
  have hslow (K : ℕ) : ∃ C : ℕ, ∀ n : ℕ, (K : ℤ) * F n ≤ (n : ℤ) + C := by
    refine ⟨P + K * K, fun n => ?_⟩
    obtain ⟨U, hU⟩ := (hX n).2.2
    have hU' := weight_bound_card b (fun i => (show i ≤ evenIndex i by change i ≤ 2 * i; omega).trans
      (seq_le_values hmono _)) U K
    rw [hU] at hU'
    have hx' := (hX n).2.1
    have hnat : K * U.card ≤ n + (P + K * K) := by omega
    rw [show F n = (U.card : ℤ) from congrArg Nat.cast (subsetSumCard_eq hb U hU)]
    exact_mod_cast hnat
  obtain ⟨B, hB⟩ := bounded_of_cross_sum_compatible F G x y
    (fun t => ⟨(hX t).1, (hX t).2.1⟩) (fun t => ⟨(hY t).1, (hY t).2.1⟩) hcross hF0 hslow
  let N := B.toNat + 1
  let z := ∑ i ∈ range N, b i
  have hz : x z = z := subsetSumCeiling_eq hx ⟨range N, rfl⟩
  have hFz : F z = (N : ℤ) := by
    dsimp only [F]
    rw [hz, subsetSumCard_eq hb (range N) rfl, card_range]
  have hle := hB z
  rw [hFz] at hle
  have hlt : B < (N : ℤ) := by dsimp [N]; omega
  exact hlt.not_ge hle

private theorem parity_deficit_often {a : ℕ → ℕ} (hmono : StrictMono a)
    (hpos : ∀ i, 0 < a i) (ha : Admissible a) (N : ℕ) :
    ∃ j ≥ N, prefixSum (fun i => a (2 * i)) j < a (2 * j) ∨
      prefixSum (fun i => a (2 * i + 1)) j < a (2 * j + 1) := by
  by_contra! h
  let P := a (2 * N + 1)
  have he (j : ℕ) : a (2 * j) ≤ prefixSum (fun i => a (2 * i)) j + P := by
    by_cases hj : N ≤ j
    · exact (h j hj).1.trans (Nat.le_add_right _ _)
    · have hle := hmono.monotone (show 2 * j ≤ 2 * N + 1 by omega)
      exact hle.trans (Nat.le_add_left _ _)
  have ho (j : ℕ) : a (2 * j + 1) ≤ prefixSum (fun i => a (2 * i + 1)) j + P := by
    by_cases hj : N ≤ j
    · exact (h j hj).2.trans (Nat.le_add_right _ _)
    · have hle := hmono.monotone (show 2 * j + 1 ≤ 2 * N + 1 by omega)
      exact hle.trans (Nat.le_add_left _ _)
  exact no_two_bounded_parity_deficits hmono hpos ha he ho

private theorem prefix_le_twice_even {a : ℕ → ℕ} (ha : Monotone a) (n : ℕ) :
    prefixSum a (2 * n + 1) ≤ 2 * prefixSum (fun i => a (2 * i)) (n + 1) := by
  induction n with
  | zero =>
      simp only [prefixSum, Nat.mul_zero, Nat.zero_add, sum_range_one]
      omega
  | succ n ih =>
      rw [show 2 * (n + 1) + 1 = (2 * n + 1 + 1) + 1 by omega,
        prefixSum_succ a (2 * n + 1 + 1), prefixSum_succ a (2 * n + 1),
        prefixSum_succ (fun i => a (2 * i)) (n + 1)]
      have h₁ := ha (show 2 * n + 1 ≤ 2 * (n + 1) by omega)
      have h₂ : 2 * n + 1 + 1 = 2 * (n + 1) := by omega
      rw [h₂]
      omega

private theorem prefix_le_twice_odd {a : ℕ → ℕ} (ha : Monotone a) (n : ℕ) :
    prefixSum a (2 * n) ≤ 2 * prefixSum (fun i => a (2 * i + 1)) n := by
  induction n with
  | zero => simp [prefixSum]
  | succ n ih =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
        prefixSum_succ a (2 * n + 1), prefixSum_succ a (2 * n),
        prefixSum_succ (fun i => a (2 * i + 1)) n]
      have h₁ := ha (show 2 * n ≤ 2 * n + 1 by omega)
      omega

private theorem two_step_large_often {a : ℕ → ℕ} (hmono : StrictMono a)
    (hpos : ∀ i, 0 < a i) (ha : Admissible a) (N : ℕ) :
    ∃ l ≥ N + 2, prefixSum a (l - 3) < 2 * (a l - a (l - 2)) := by
  obtain ⟨j, hj, he | ho⟩ := parity_deficit_often hmono hpos ha (N + 2)
  · refine ⟨2 * j, by omega, ?_⟩
    have hj' : j = (j - 1) + 1 := by omega
    have hprev := prefixSum_succ (fun i => a (2 * i)) (j - 1)
    rw [← hj'] at hprev
    have h₂ := prefix_le_twice_even hmono.monotone (j - 2)
    have h₃ : 2 * (j - 2) + 1 = 2 * j - 3 := by omega
    have h₄ : j - 2 + 1 = j - 1 := by omega
    have h₅ : 2 * (j - 1) = 2 * j - 2 := by omega
    rw [h₃, h₄] at h₂
    simp only [h₅] at hprev
    omega
  · refine ⟨2 * j + 1, by omega, ?_⟩
    have hj' : j = (j - 1) + 1 := by omega
    have hprev := prefixSum_succ (fun i => a (2 * i + 1)) (j - 1)
    rw [← hj'] at hprev
    have h₂ := prefix_le_twice_odd hmono.monotone (j - 1)
    have h₃ : 2 * (j - 1) = 2 * j + 1 - 3 := by omega
    have h₄ : 2 * (j - 1) + 1 = 2 * j + 1 - 2 := by omega
    rw [h₃] at h₂
    simp only [h₄] at hprev
    omega

/-- The large-gap assertion of Howe–Huffman–Kohlmeyer–Kruer, Lemma 2.1.
The index is zero-based and the factor four is moved to the right in natural arithmetic. -/
theorem large_gaps_often {a : ℕ → ℕ} (hmono : StrictMono a) (hpos : ∀ i, 0 < a i)
    (ha : Admissible a) (N : ℕ) :
    ∃ n ≥ N, (∑ i ∈ range (n - 2), a i) < 4 * gap a n := by
  obtain ⟨l, hl, hgap⟩ := two_step_large_often hmono hpos ha N
  have h₁ : l - 2 + 1 = l - 1 := by omega
  have h₂ : l - 1 + 1 = l := by omega
  have hsplit : gap a (l - 2) + gap a (l - 1) = a l - a (l - 2) := by
    unfold gap
    rw [h₁, h₂]
    have hl₁ := hmono.monotone (show l - 2 ≤ l - 1 by omega)
    have hl₂ := hmono.monotone (Nat.sub_le l 1)
    omega
  rcases le_total (gap a (l - 1)) (gap a (l - 2)) with h | h
  · refine ⟨l - 2, by omega, ?_⟩
    have hp : prefixSum a (l - 2 - 2) ≤ prefixSum a (l - 3) :=
      sum_le_sum_of_subset (range_mono (by omega))
    change prefixSum a (l - 2 - 2) < _
    omega
  · refine ⟨l - 1, by omega, ?_⟩
    have hp : l - 1 - 2 = l - 3 := by omega
    change prefixSum a (l - 1 - 2) < _
    rw [hp]
    omega

end Jsp000726
