module

public import Jsp000726.UpperLimit

@[expose] public section

namespace Jsp000726.Upper

/-- Gap bounds on a finite block, with indices counted from its position in the prefix. -/
def IndexedGapBound (c : ℝ) (offset : ℕ) (l : List ℕ) : Prop :=
  ∀ n (hn : n + 1 < l.length),
    ((l[n + 1] - l[n] : ℕ) : ℝ) ≤ ((offset + n + 1 : ℕ) : ℝ) ^ c

/-- The gap bound on a concatenation follows from its two blocks and their boundary. -/
theorem indexedGapBound_append {c : ℝ} {offset : ℕ} {L R : List ℕ}
    (hL : IndexedGapBound c offset L) (hR : IndexedGapBound c (offset + L.length) R)
    (hbridge : ∀ (hLne : 0 < L.length) (hRne : 0 < R.length),
      ((R[0] - L[L.length - 1]'(by omega) : ℕ) : ℝ) ≤ ((offset + L.length : ℕ) : ℝ) ^ c) :
    IndexedGapBound c offset (L ++ R) := by
  intro n hn
  have htotal : n + 1 < L.length + R.length := by simpa using hn
  by_cases hleft : n + 1 < L.length
  · simpa only [List.getElem_append_left (show n < L.length by omega),
      List.getElem_append_left hleft] using hL n hleft
  by_cases hnleft : n < L.length
  · have hboundary : n + 1 = L.length := by omega
    have hRne : 0 < R.length := by omega
    rw [List.getElem_append_left hnleft, List.getElem_append_right (by omega : L.length ≤ n + 1)]
    have hi : n + 1 - L.length = 0 := by omega
    have hj : n = L.length - 1 := by omega
    have hindex : offset + n + 1 = offset + L.length := by omega
    simp only [hindex]
    convert hbridge (by omega) hRne using 2; congr
  · let j := n - L.length
    have hj : j + 1 < R.length := by dsimp [j]; omega
    have hn' : n = L.length + j := by dsimp [j]; omega
    have h1 : n + 1 - L.length = j + 1 := by dsimp [j]; omega
    have hindex : offset + n + 1 = offset + L.length + j + 1 := by omega
    rw [List.getElem_append_right (by omega : L.length ≤ n),
      List.getElem_append_right (by omega : L.length ≤ n + 1), hindex]
    convert hR j hj using 2; congr

/-- A seed and a closed extension rule produce a global gap witness. -/
theorem gapExponent_of_extension {α : Type*} (c : ℝ) (P : α → Prop)
    (terms : α → List ℕ) (seed : α) (hseed : P seed)
    (hstep : ∀ s, P s → ∃ t, P t ∧ List.IsPrefix (terms s) (terms t) ∧
      (terms s).length < (terms t).length)
    (hsorted : ∀ s, P s → (terms s).Pairwise (· < ·))
    (hpos : ∀ s, P s → ∀ x ∈ terms s, 0 < x)
    (hadm : ∀ s, P s → ∀ U V : Finset ℤ, U ⊆ (terms s |>.map (↑)).toFinset →
      V ⊆ (terms s |>.map (↑)).toFinset → (∑ x ∈ U, x) = (∑ x ∈ V, x) → U.card = V.card)
    (hgaps : ∀ s, P s → IndexedGapBound c 0 (terms s)) :
    GapExponent c := by
  classical
  let next (s : {x // P x}) : {x // P x} :=
    ⟨Classical.choose (hstep s.val s.property), (Classical.choose_spec
      (hstep s.val s.property)).1⟩
  let states : ℕ → {x // P x} := fun n => Nat.rec ⟨seed, hseed⟩ (fun _ s => next s) n
  let p (n : ℕ) := terms (states n).val
  have hnext n : List.IsPrefix (p n) (p (n + 1)) ∧ (p n).length < (p (n + 1)).length :=
    (Classical.choose_spec (hstep (states n).val (states n).property)).2
  apply gapExponent_of_prefixes c p (fun n => (hnext n).1) (fun n => (hnext n).2)
    (fun n => hsorted _ (states n).property) (fun n => hpos _ (states n).property)
    (fun n => hadm _ (states n).property)
  intro k n hn
  simpa only [IndexedGapBound, zero_add, Nat.cast_add, Nat.cast_one] using
    hgaps (states k).val (states k).property n hn

end Jsp000726.Upper
