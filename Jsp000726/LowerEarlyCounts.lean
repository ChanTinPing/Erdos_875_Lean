module

public import Jsp000726.LowerCounting
public import Mathlib.Data.Finset.Max

@[expose] public section

namespace Jsp000726

open Finset

def prefixWeight (a : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ range n, a i

theorem prefixWeight_succ (a : ℕ → ℕ) (n : ℕ) :
    prefixWeight a (n + 1) = prefixWeight a n + a n := Finset.sum_range_succ a n

theorem prefixWeight_mono (a : ℕ → ℕ) : Monotone (prefixWeight a) :=
  fun _ _ h => sum_le_sum_of_subset (range_mono h)

theorem le_prefixWeight {a : ℕ → ℕ} (ha : ∀ n, 0 < a n) (n : ℕ) : n ≤ prefixWeight a n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      rw [prefixWeight_succ]
      have h := ha n
      omega

def prefixCandidates (a : ℕ → ℕ) (x : ℕ) : Finset ℕ :=
  (range (x + 1)).filter fun j => prefixWeight a j ≤ x

theorem prefixCandidates_nonempty (a : ℕ → ℕ) (x : ℕ) : (prefixCandidates a x).Nonempty :=
  ⟨0, mem_filter.mpr ⟨mem_range.mpr (Nat.zero_lt_succ x), by simp [prefixWeight]⟩⟩

/-- The last prefix whose total weight stays at most `x`, for positive sequences. -/
def prefixAt (a : ℕ → ℕ) (x : ℕ) : ℕ :=
  (prefixCandidates a x).max' (prefixCandidates_nonempty a x)

theorem prefixWeight_at_le (a : ℕ → ℕ) (x : ℕ) : prefixWeight a (prefixAt a x) ≤ x :=
  (mem_filter.mp ((prefixCandidates a x).max'_mem (prefixCandidates_nonempty a x))).2

theorem prefixAt_lt_prefixWeight_succ {a : ℕ → ℕ} (ha : ∀ n, 0 < a n) (x : ℕ) :
    x < prefixWeight a (prefixAt a x + 1) := by
  by_contra! hx
  have hidx : prefixAt a x + 1 ≤ x := (le_prefixWeight ha _).trans hx
  have hm : prefixAt a x + 1 ∈ prefixCandidates a x := mem_filter.mpr ⟨mem_range.mpr (by omega), hx⟩
  have hmax : prefixAt a x + 1 ≤ prefixAt a x := (prefixCandidates a x).le_max' _ hm
  omega

/-- Total number of subset-sum values on a prefix. -/
def allCounts (a : ℕ → ℕ) (n : ℕ) : ℕ := (sumValues a (range n)).card

/-- Number of subset-sum values in the middle layer of a prefix. -/
def middleLayer (a : ℕ → ℕ) (n : ℕ) : ℕ := (sumLayer a (range n) (n / 2)).card

def layerCounts (a : ℕ → ℕ) (n : ℕ) : Finset ℕ :=
  (range (n + 1)).image fun r => (sumLayer a (range n) r).card

theorem layerCounts_nonempty (a : ℕ → ℕ) (n : ℕ) : (layerCounts a n).Nonempty :=
  ⟨_, mem_image.mpr ⟨0, by simp, rfl⟩⟩

/-- The size of a largest fixed-cardinality layer on a prefix. -/
def largestLayer (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  (layerCounts a n).max' (layerCounts_nonempty a n)

theorem exists_layer_card_eq_largestLayer (a : ℕ → ℕ) (n : ℕ) :
    ∃ r ≤ n, (sumLayer a (range n) r).card = largestLayer a n := by
  obtain ⟨r, hr, heq⟩ := mem_image.mp ((layerCounts a n).max'_mem (layerCounts_nonempty a n))
  exact ⟨r, Nat.lt_succ_iff.mp (mem_range.mp hr), heq⟩

theorem card_sumLayer_le_largestLayer (a : ℕ → ℕ) {n r : ℕ} (hr : r ≤ n) :
    (sumLayer a (range n) r).card ≤ largestLayer a n := by
  exact (layerCounts a n).le_max' _ (mem_image.mpr ⟨r, mem_range.mpr (Nat.lt_succ_iff.mpr hr), rfl⟩)

theorem middleLayer_le_largestLayer (a : ℕ → ℕ) (n : ℕ) : middleLayer a n ≤ largestLayer a n :=
  card_sumLayer_le_largestLayer a (Nat.div_le_self n 2)

theorem allCounts_le_prefixWeight_add_one (a : ℕ → ℕ) (n : ℕ) :
    allCounts a n ≤ prefixWeight a n + 1 := card_sumValues_le_sum_add_one _ _

theorem succ_le_allCounts {a : ℕ → ℕ} (hmono : StrictMono a) (hpos : ∀ n, 0 < a n) (n : ℕ) :
    n + 1 ≤ allCounts a n := by
  have hsubset : insert 0 ((range n).image a) ⊆ sumValues a (range n) := by
    intro x hx
    rcases mem_insert.mp hx with hzero | hrest
    · exact mem_sumValues.mpr ⟨∅, empty_subset _, by simp [hzero]⟩
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp hrest
      exact mem_sumValues.mpr ⟨{i}, singleton_subset_iff.mpr hi, sum_singleton _ _⟩
  have hnot : 0 ∉ (range n).image a := by
    intro h
    obtain ⟨i, _, hi⟩ := mem_image.mp h
    exact (hpos i).ne' hi
  have h := card_le_card hsubset
  rwa [card_insert_of_notMem hnot, card_image_of_injective _ hmono.injective, card_range] at h

theorem allCounts_le_mul_largestLayer {a : ℕ → ℕ} (ha : Admissible a) (n : ℕ) :
    allCounts a n ≤ (n + 1) * largestLayer a n := by
  let V (r : ℕ) := sumLayer a (range n) r
  have hsubset : sumValues a (range n) ⊆ (range (n + 1)).biUnion V := by
    intro x hx
    obtain ⟨U, hU, hsum⟩ := mem_sumValues.mp hx
    have hr : U.card ≤ n := by simpa only [card_range] using card_le_card hU
    exact mem_biUnion.mpr ⟨U.card, mem_range.mpr (Nat.lt_succ_iff.mpr hr),
      mem_sumLayer.mpr ⟨U, hU, rfl, hsum⟩⟩
  have hdis : (range (n + 1) : Set ℕ).PairwiseDisjoint V :=
    fun _ _ _ _ hrq => disjoint_sumLayer_of_ne ha _ hrq
  have h := card_le_card hsubset
  rw [card_biUnion hdis] at h
  refine h.trans ?_
  have hl : ∑ r ∈ range (n + 1), (V r).card ≤ ∑ _r ∈ range (n + 1), largestLayer a n := by
    refine sum_le_sum fun r hr => card_sumLayer_le_largestLayer a ?_
    exact Nat.lt_succ_iff.mp (mem_range.mp hr)
  simpa only [sum_const, card_range, nsmul_eq_mul, Nat.cast_id] using hl

theorem middleLayer_half_mul_le_allCounts {a : ℕ → ℕ} (ha : Admissible a) (n : ℕ) :
    middleLayer a (n / 2) * (n - n / 2 + 1) ≤ allCounts a n := by
  let R := range (n / 2)
  let S := range n \ R
  have hR : R ⊆ range n := range_mono (Nat.div_le_self n 2)
  have hdis : Disjoint R S := disjoint_sdiff
  have hu : R ∪ S = range n := by
    ext i
    by_cases hi : i ∈ R
    · have hni := hR hi
      simp [S, hi, hni]
    · simp [S, hi]
  have hc : S.card = n - n / 2 := by rw [card_sdiff_of_subset hR]; simp [R]
  have h := card_sumLayer_mul_succ_le_sumValues ha hdis ((n / 2) / 2)
  rw [hu, hc] at h
  exact h

/-- Exact prefix form of the heavy-threshold bound used to feed the moment estimate. -/
theorem earlyCount_mul_heavyCount_le {a : ℕ → ℕ} {n H : ℕ} (hH : 0 < H)
    (hR : prefixAt a (H / 8) ≤ n) :
    allCounts a (prefixAt a (H / 8)) * (((range n).filter fun i => H ≤ a i).card + 1)
      ≤ allCounts a n := by
  let R := range (prefixAt a (H / 8))
  let S := (range n).filter fun i => H ≤ a i
  have hR' : (∑ i ∈ R, a i) ≤ H / 8 := prefixWeight_at_le _ _
  have hsmall : (∑ i ∈ R, a i) < H := hR'.trans_lt (Nat.div_lt_self hH (by decide))
  have hdis : Disjoint R S := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hh := (mem_filter.mp hj).2
    have hw : a i ≤ ∑ j ∈ R, a j := single_le_sum (fun _ _ => Nat.zero_le _) hi
    exact (not_lt_of_ge (hh.trans hw)) hsmall
  have hS : ∀ i ∈ S, H ≤ a i := fun _ hi => (mem_filter.mp hi).2
  have h := card_sumValues_mul_succ_le_of_small_and_large hdis hH hsmall hS
  have hU : R ∪ S ⊆ range n := union_subset (range_mono hR) (filter_subset _ _)
  exact h.trans (card_le_card (sumValues_mono hU))

end Jsp000726
