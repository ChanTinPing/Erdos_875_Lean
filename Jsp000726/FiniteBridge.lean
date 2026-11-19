module

public import Jsp000726.Basic
public import Mathlib.Data.Finset.Preimage
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace Jsp000726

/-- The original admissibility predicate on values, independent of any enumeration. -/
def SetAdmissible (A : Set ℕ) : Prop :=
  ∀ U V : Finset ℕ, (U : Set ℕ) ⊆ A → (V : Set ℕ) ⊆ A →
    (∑ x ∈ U, x) = (∑ x ∈ V, x) → U.card = V.card

/-- A strictly increasing enumeration may use subsets of indices or subsets of values. -/
theorem admissible_iff_setAdmissible_range {a : ℕ → ℕ} (ha : StrictMono a) :
    Admissible a ↔ SetAdmissible (Set.range a) := by
  let f : ℕ ↪ ℕ := ⟨a, ha.injective⟩
  have hf (i : ℕ) : f i = a i := rfl
  constructor
  · intro h U V hU hV hsum
    have mapPreimage (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ Set.range a) :
        (S.preimage a ha.injective.injOn).map f = S := by
      ext x
      constructor
      · intro hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
        exact Finset.mem_preimage.mp hi
      · intro hx
        obtain ⟨i, hi⟩ := hS hx
        exact Finset.mem_map.mpr ⟨i, Finset.mem_preimage.mpr (hi ▸ hx), hi⟩
    rw [← mapPreimage U hU, ← mapPreimage V hV] at hsum ⊢
    simpa only [Finset.card_map] using
      h (U.preimage a ha.injective.injOn) (V.preimage a ha.injective.injOn)
        (by simpa only [Finset.sum_map, hf] using hsum)
  · intro h U V hsum
    have mappedSubset (S : Finset ℕ) : (↑(S.map f) : Set ℕ) ⊆ Set.range a := by
      intro x hx
      obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hx
      exact ⟨i, hi⟩
    simpa only [Finset.card_map] using
      h (U.map f) (V.map f) (mappedSubset U) (mappedSubset V)
        (by simpa only [Finset.sum_map, hf] using hsum)

/-- An exhaustion by finite admissible prefixes transfers the property to the enumeration. -/
theorem admissible_of_integer_prefixes {a : ℕ → ℕ} (ha : StrictMono a)
    (A : ℕ → Finset ℤ) (hmono : Monotone A)
    (hcover : ∀ i : ℕ, ∃ k, (a i : ℤ) ∈ A k)
    (hA : ∀ k (U V : Finset ℤ), U ⊆ A k → V ⊆ A k →
      (∑ x ∈ U, x) = (∑ x ∈ V, x) → U.card = V.card) :
    Admissible a := by
  let f : ℕ ↪ ℤ := Function.Embedding.trans ⟨a, ha.injective⟩ Nat.castEmbedding
  have hf (i : ℕ) : f i = (a i : ℤ) := rfl
  have covered (S : Finset ℕ) : ∃ k, S.map f ⊆ A k := by
    classical
    induction S using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨j, hj⟩ := hcover i
      obtain ⟨k, hk⟩ := ih
      refine ⟨max j k, ?_⟩
      rw [Finset.map_insert]
      exact Finset.insert_subset_iff.mpr
        ⟨hmono (le_max_left j k) hj, hk.trans (hmono (le_max_right j k))⟩
  intro U V hsum
  obtain ⟨j, hj⟩ := covered U
  obtain ⟨k, hk⟩ := covered V
  have hsumInt : (∑ x ∈ U.map f, x) = ∑ x ∈ V.map f, x := by
    have hcast := congrArg (fun n : ℕ => (n : ℤ)) hsum
    simpa only [Finset.sum_map, Nat.cast_sum, hf] using hcast
  simpa only [Finset.card_map] using
    hA (max j k) (U.map f) (V.map f) (hj.trans (hmono (le_max_left j k)))
      (hk.trans (hmono (le_max_right j k))) hsumInt

end Jsp000726
