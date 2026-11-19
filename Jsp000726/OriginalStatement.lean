module

public import Jsp000726.FiniteBridge
public import Mathlib.Data.Nat.Nth

@[expose] public section

namespace Jsp000726

open Filter Finset

/-- Sums of exactly `r` distinct values of `A`, as in the original problem. -/
def originalRSums (A : Set ℕ) (r : ℕ) : Set ℕ :=
  {s | ∃ T : Finset ℕ, (T : Set ℕ) ⊆ A ∧ T.card = r ∧ ∑ x ∈ T, x = s}

/-- The positive-cardinality layers specified in Erdős #875 are pairwise disjoint. -/
def OriginalAdmissible (A : Set ℕ) : Prop :=
  (Set.Ici (1 : ℕ)).PairwiseDisjoint (originalRSums A)

/-- The gap indexed starting at one, matching Formal Conjectures' `Nat.nth` statement. -/
noncomputable def originalGap (A : Set ℕ) (n : ℕ) : ℕ :=
  Nat.nth (· ∈ A) n - Nat.nth (· ∈ A) (n - 1)

def OriginalGapExponent (c : ℝ) : Prop :=
  ∃ A : Set ℕ, A.Infinite ∧ OriginalAdmissible A ∧
    ∀ n : ℕ, 1 ≤ n → (originalGap A n : ℝ) ≤ (n : ℝ) ^ c

def OriginalEventualGapExponent (c : ℝ) : Prop :=
  ∃ A : Set ℕ, A.Infinite ∧ OriginalAdmissible A ∧
    ∀ᶠ n : ℕ in atTop, (originalGap A n : ℝ) ≤ (n : ℝ) ^ c

theorem originalAdmissible_of_setAdmissible {A : Set ℕ} (hA : SetAdmissible A) :
    OriginalAdmissible A := by
  intro r _ q _ hrq
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨U, hU, hr, hs⟩ := hx
  obtain ⟨V, hV, hq, ht⟩ := hy
  exact hrq (hr.symm.trans ((hA U V hU hV (hs.trans ht.symm)).trans hq))

/-- Zero cannot occur in an infinite admissible value set, since adjoining it to
a nonzero singleton creates a collision between the first two layers. -/
theorem OriginalAdmissible.zero_notMem {A : Set ℕ} (hA : A.Infinite)
    (hAdm : OriginalAdmissible A) : 0 ∉ A := by
  intro h0
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ A, x ≠ 0 := by
    by_contra! h
    exact hA ((Set.finite_singleton (0 : ℕ)).subset (fun i hi => Set.mem_singleton_iff.mpr (h i hi)))
  have h1 : x ∈ originalRSums A 1 := ⟨{x}, by simpa using hx, by simp, by simp⟩
  have h2 : x ∈ originalRSums A 2 := by
    have hne : (0 : ℕ) ∉ ({x} : Finset ℕ) := by simpa only [mem_singleton] using hx0.symm
    refine ⟨insert 0 {x}, ?_, ?_, ?_⟩
    · intro i hi
      rcases mem_insert.mp hi with rfl | hi
      · exact h0
      · have he := mem_singleton.mp hi
        exact he ▸ hx
    · rw [card_insert_of_notMem hne, card_singleton]
    · rw [sum_insert hne, sum_singleton, zero_add]
  have hd : Disjoint (originalRSums A 1) (originalRSums A 2) :=
    hAdm (show (1 : ℕ) ∈ Set.Ici 1 by decide) (show (2 : ℕ) ∈ Set.Ici 1 by decide) (by decide)
  exact (Set.disjoint_left.mp hd h1 h2)

theorem originalAdmissible_iff_setAdmissible {A : Set ℕ} (hA : A.Infinite) :
    OriginalAdmissible A ↔ SetAdmissible A := by
  refine ⟨?_, originalAdmissible_of_setAdmissible⟩
  intro hAdm U V hU hV hsum
  have hzero : ∀ T : Finset ℕ, (T : Set ℕ) ⊆ A → (∑ i ∈ T, i) = 0 → T.card = 0 := by
    intro T hT hs
    by_contra! hc
    obtain ⟨i, hi⟩ := card_pos.mp (Nat.pos_of_ne_zero hc)
    have hi0 : i ≠ 0 := fun h => hAdm.zero_notMem hA (h ▸ hT hi)
    have hle : i ≤ ∑ x ∈ T, x := single_le_sum (f := id) (fun x _ => Nat.zero_le x) hi
    omega
  by_cases hUc : U.card = 0
  · have hsumU : (∑ x ∈ U, x) = 0 := by rw [card_eq_zero.mp hUc, sum_empty]
    exact hUc.trans (hzero V hV (hsum.symm.trans hsumU)).symm
  by_cases hVc : V.card = 0
  · have hsumV : (∑ x ∈ V, x) = 0 := by rw [card_eq_zero.mp hVc, sum_empty]
    exact (hzero U hU (hsum.trans hsumV)).trans hVc.symm
  by_contra hne
  have hd : Disjoint (originalRSums A U.card) (originalRSums A V.card) :=
    hAdm (show U.card ∈ Set.Ici 1 by simpa using Nat.pos_of_ne_zero hUc)
      (show V.card ∈ Set.Ici 1 by simpa using Nat.pos_of_ne_zero hVc) hne
  exact Set.disjoint_left.mp hd ⟨U, hU, rfl, rfl⟩ ⟨V, hV, rfl, hsum.symm⟩

private theorem nth_range_eq_of_strictMono {a : ℕ → ℕ} (ha : StrictMono a) :
    Nat.nth (· ∈ Set.range a) = a := by
  have hinf : (Set.range a).Infinite := Set.infinite_range_of_injective ha.injective
  have hi (i : ℕ) : ∀ hf : (Set.range a).Finite, i < hf.toFinset.card :=
    fun hf => (hinf hf).elim
  funext i
  refine (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn (p := (· ∈ Set.range a)) a ?_ ?_
    (ha.strictMonoOn _) (hi i)).symm
  · rintro _ ⟨j, rfl⟩
    exact ⟨j, hi j, rfl⟩
  · exact fun j _ => ⟨j, rfl⟩

/-- The paper's first gap is the gap at index zero in the sequence proof. -/
theorem originalGap_succ (A : Set ℕ) (k : ℕ) :
    originalGap A (k + 1) = gap (Nat.nth (· ∈ A)) k := by
  rw [originalGap, gap, Nat.add_sub_cancel]

theorem originalGap_bounds_iff (A : Set ℕ) (c : ℝ) :
    (∀ n : ℕ, 1 ≤ n → (originalGap A n : ℝ) ≤ (n : ℝ) ^ c) ↔
    (∀ n : ℕ, (gap (Nat.nth (· ∈ A)) n : ℝ) ≤ (n + 1 : ℝ) ^ c) := by
  constructor
  · intro h n
    simpa only [originalGap_succ, Nat.cast_add, Nat.cast_one] using h (n + 1) (by omega)
  · intro h n hn
    have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
    have h' : (originalGap A (n - 1 + 1) : ℝ) ≤ ((n - 1 + 1 : ℕ) : ℝ) ^ c := by
      rw [originalGap_succ, Nat.cast_add, Nat.cast_one]
      apply h
    rwa [hn'] at h'

theorem originalGap_eventual_bounds_iff (A : Set ℕ) (c : ℝ) :
    (∀ᶠ n : ℕ in atTop, (originalGap A n : ℝ) ≤ (n : ℝ) ^ c) ↔
    (∀ᶠ n : ℕ in atTop, (gap (Nat.nth (· ∈ A)) n : ℝ) ≤ (n + 1 : ℝ) ^ c) := by
  rw [eventually_atTop, eventually_atTop]
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨N, fun n hn => by
      simpa only [originalGap_succ, Nat.cast_add, Nat.cast_one] using hN (n + 1) (by omega)⟩
  · rintro ⟨N, hN⟩
    refine ⟨N + 1, fun n hn => ?_⟩
    have hn' : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
    have h' : (originalGap A (n - 1 + 1) : ℝ) ≤ ((n - 1 + 1 : ℕ) : ℝ) ^ c := by
      rw [originalGap_succ, Nat.cast_add, Nat.cast_one]
      exact hN (n - 1) (by omega)
    rwa [hn'] at h'

private theorem nth_enumerates_original_admissible {A : Set ℕ} (hA : A.Infinite)
    (hAdm : OriginalAdmissible A) :
    let a := Nat.nth (· ∈ A)
    StrictMono a ∧ (∀ n, 0 < a n) ∧ Admissible a := by
  let a := Nat.nth (· ∈ A)
  have hmono : StrictMono a := Nat.nth_strictMono hA
  have hrange : Set.range a = A := Nat.range_nth_of_infinite hA
  refine ⟨hmono, ?_, (admissible_iff_setAdmissible_range hmono).mpr ?_⟩
  · intro n
    exact Nat.pos_of_ne_zero fun hn => hAdm.zero_notMem hA (hn ▸ Nat.nth_mem_of_infinite hA n)
  · rw [hrange]
    exact (originalAdmissible_iff_setAdmissible hA).mp hAdm

theorem originalGapExponent_iff (c : ℝ) : OriginalGapExponent c ↔ GapExponent c := by
  constructor
  · rintro ⟨A, hA, hAdm, hgap⟩
    obtain ⟨hmono, hpos, ha⟩ := nth_enumerates_original_admissible hA hAdm
    exact ⟨Nat.nth (· ∈ A), hmono, hpos, ha, (originalGap_bounds_iff A c).mp hgap⟩
  · rintro ⟨a, hmono, _, ha, hgap⟩
    refine ⟨Set.range a, Set.infinite_range_of_injective hmono.injective,
      originalAdmissible_of_setAdmissible ((admissible_iff_setAdmissible_range hmono).mp ha), ?_⟩
    apply (originalGap_bounds_iff (Set.range a) c).mpr
    simpa only [nth_range_eq_of_strictMono hmono] using hgap

/-- The eventual convention is precisely the form used by Formal Conjectures'
Erdős #875 statement, with the same one-based use of `Nat.nth`. -/
theorem originalEventualGapExponent_iff (c : ℝ) :
    OriginalEventualGapExponent c ↔ EventualGapExponent c := by
  constructor
  · rintro ⟨A, hA, hAdm, hgap⟩
    obtain ⟨hmono, hpos, ha⟩ := nth_enumerates_original_admissible hA hAdm
    exact ⟨Nat.nth (· ∈ A), hmono, hpos, ha, (originalGap_eventual_bounds_iff A c).mp hgap⟩
  · rintro ⟨a, hmono, _, ha, hgap⟩
    refine ⟨Set.range a, Set.infinite_range_of_injective hmono.injective,
      originalAdmissible_of_setAdmissible ((admissible_iff_setAdmissible_range hmono).mp ha), ?_⟩
    apply (originalGap_eventual_bounds_iff (Set.range a) c).mpr
    simpa only [nth_range_eq_of_strictMono hmono] using hgap

/-- The exact set-based statement, in both the all-index and the eventual conventions,
follows from the two sequence bounds. -/
theorem sharpOriginalGapStatements_of_bounds (hupper : GapExponent gapThreshold)
    (hlower : ∀ c : ℝ, EventualGapExponent c → gapThreshold ≤ c) :
    {c : ℝ | OriginalGapExponent c} = Set.Ici ((5 + Real.sqrt 17) / 2) ∧
    {c : ℝ | OriginalEventualGapExponent c} = Set.Ici ((5 + Real.sqrt 17) / 2) := by
  obtain ⟨hsharp, hsharpEventually⟩ := sharpGapStatements_of_bounds hupper hlower
  have hset : {c : ℝ | OriginalGapExponent c} = {c : ℝ | GapExponent c} :=
    Set.ext (fun c => originalGapExponent_iff c)
  have hsetEventually : {c : ℝ | OriginalEventualGapExponent c} = {c : ℝ | EventualGapExponent c} :=
    Set.ext (fun c => originalEventualGapExponent_iff c)
  exact ⟨hset.trans hsharp, hsetEventually.trans hsharpEventually⟩

end Jsp000726
