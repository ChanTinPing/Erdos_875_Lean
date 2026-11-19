module

public import Jsp000726.FiniteBridge
public import Mathlib.Data.Finset.Basic

@[expose] public section

namespace Jsp000726.Upper

/-- Assemble nested finite constructions with certified gaps into one infinite witness. -/
theorem gapExponent_of_prefixes (c : ℝ) (p : ℕ → List ℕ)
    (hprefix : ∀ k, List.IsPrefix (p k) (p (k + 1)))
    (hgrowing : ∀ k, (p k).length < (p (k + 1)).length)
    (hsorted : ∀ k, (p k).Pairwise (· < ·))
    (hpositive : ∀ k x, x ∈ p k → 0 < x)
    (hadmissible : ∀ k (U V : Finset ℤ), U ⊆ (p k |>.map (↑)).toFinset →
      V ⊆ (p k |>.map (↑)).toFinset → (∑ x ∈ U, x) = (∑ x ∈ V, x) → U.card = V.card)
    (hgap : ∀ k n (hn : n + 1 < (p k).length),
      (((p k)[n + 1] - (p k)[n] : ℕ) : ℝ) ≤ (n + 1 : ℝ) ^ c) :
    GapExponent c := by
  have hle : ∀ i j : ℕ, i ≤ j → List.IsPrefix (p i) (p j) := by
    intro i j hij
    induction hij with
    | refl => exact ⟨[], by simp⟩
    | step _ ih => exact ih.trans (hprefix _)
  have hlength : ∀ k, k ≤ (p k).length := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih => exact Nat.succ_le_of_lt (ih.trans_lt (hgrowing k))
  let a (n : ℕ) : ℕ := (p (n + 1))[n]'(Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (hlength _))
  have hat (n k : ℕ) (hn : n < (p k).length) : a n = (p k)[n] := by
    rcases le_total (n + 1) k with h | h
    · exact (hle _ _ h).getElem _
    · exact ((hle _ _ h).getElem hn).symm
  have hamono : StrictMono a := by
    intro i j hij
    have hj : j < (p (j + 1)).length := (Nat.lt_succ_self j).trans_le (hlength _)
    rw [hat i (j + 1) (hij.trans hj), hat j (j + 1) hj]
    exact (hsorted (j + 1)).rel_getElem_of_lt _ _ hij
  refine ⟨a, hamono, ?_, ?_, ?_⟩
  · intro n
    exact hpositive _ _ (List.getElem_mem _)
  · let A (k : ℕ) : Finset ℤ := ((p k).map (↑)).toFinset
    apply admissible_of_integer_prefixes hamono A _ _ hadmissible
    · intro i j hij x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨y, (hle _ _ hij).subset hy, rfl⟩)
    · intro n
      refine ⟨n + 1, List.mem_toFinset.mpr ?_⟩
      exact List.mem_map.mpr ⟨a n, List.getElem_mem _, rfl⟩
  · intro n
    have hn : n + 1 < (p (n + 2)).length := (Nat.lt_succ_self (n + 1)).trans_le (hlength _)
    simpa only [gap, hat (n + 1) (n + 2) hn,
      hat n (n + 2) ((Nat.lt_succ_self n).trans hn)] using hgap (n + 2) n hn

end Jsp000726.Upper
