module

public import Jsp000726.UpperBlock
public import Jsp000726.UpperMass
public import Jsp000726.UpperRowEstimates
public import Jsp000726.UpperStage

import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators

namespace Jsp000726.Upper

/-- View a list of natural terms as the finite integer set used by the invariant. -/
def integerTerms (a : List ℕ) : Finset ℤ := (a.map Int.ofNat).toFinset

theorem mem_integerTerms {a : List ℕ} {x : ℤ} :
    x ∈ integerTerms a ↔ ∃ n ∈ a, (n : ℤ) = x := by
  simp [integerTerms]

@[simp] theorem integerTerms_append (a b : List ℕ) :
    integerTerms (a ++ b) = integerTerms a ∪ integerTerms b := by
  simp [integerTerms, List.toFinset_append]

theorem integerTerms_card_le (a : List ℕ) : (integerTerms a).card ≤ a.length := by
  simpa [integerTerms] using (a.map Int.ofNat).toFinset_card_le

private theorem fillerTerms_eq_image (B g h N r H : ℕ) :
    integerTerms (fillerBlock B g h N r H) =
      (Finset.range r).image (fun i => (fillerValue B g h N r H i : ℤ)) := by
  ext x
  simp [integerTerms, fillerBlock, List.mem_range, Function.comp_def]

private theorem block_terms_disjoint {a : List ℕ} {B g h N r H R k : ℕ}
    (ha : ∀ x ∈ a, x < B) (hN : 0 < N) (hh : 0 < h) (hg : 0 < g) (hgn : h * N ≤ g)
    (hH : 0 < H) (hR : r ^ 3 / N ^ 3 + H = R - k) :
    Disjoint (integerTerms a) (integerTerms (fillerBlock B g h N r H)) ∧
    Disjoint (integerTerms a ∪ integerTerms (fillerBlock B g h N r H))
      (integerTerms (denseBlock B g R k)) := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨n, hn, rfl⟩ := mem_integerTerms.mp hx
    obtain ⟨y, hy, hey⟩ := mem_integerTerms.mp hy
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hy
    have hnB := ha n hn
    have he : fillerValue B g h N r H i = n := by exact_mod_cast hey
    unfold fillerValue at he
    omega
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨y, hyL, heY⟩ := mem_integerTerms.mp hy
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hyL
    subst x
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨n, hn, he⟩ := mem_integerTerms.mp hx
      have hnB := ha n hn
      have hn : n = denseValue B g R k j := by exact_mod_cast he
      unfold denseValue at hn
      omega
    · obtain ⟨y, hy, he⟩ := mem_integerTerms.mp hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
      have hf := fillerValue_lt_dense_zero (B := B) hN hh hgn hH hR (List.mem_range.mp hi)
      have hd := (denseValue_strictMono (B := B) (R := R) (k := k) hg).monotone (Nat.zero_le j)
      have he' : fillerValue B g h N r H i = denseValue B g R k j := by exact_mod_cast he
      omega

/-- The explicit filler and dense blocks preserve the invariant with a renewed budget. -/
theorem concrete_extend_prefix {a : List ℕ} {B h d K r k R H : ℕ}
    (hN : 2 ≤ a.length) (hB : 0 < B) (hh : 0 < h) (hd : 0 < d)
    (hdK : d ∣ K) (hdiv : h ∣ B * K)
    (hNr : a.length ≤ r) (hK : 16 * r ≤ K) (hsize : a.length + r ≤ k) (hkR : k ≤ R)
    (hH : 0 < H) (hR : r ^ 3 / a.length ^ 3 + H = R - k)
    (hreference : 64 * B * k ^ 2 ≤ B + B * K * R)
    (ha : ∀ x ∈ a, x < B) (hi : invariant (integerTerms a) B h d)
    (hb : mass (integerTerms a) B + 10 * (h : ℤ) * (a.length : ℤ) ^ 2 < (B : ℤ) * d) :
    let g := B * K
    let B' := B + g * R
    let a' := extendPrefix a B g h a.length r H R k
    invariant (integerTerms a') B' g K ∧
      mass (integerTerms a') B' + 10 * (g : ℤ) * (a'.length : ℤ) ^ 2 < (B' : ℤ) * K := by
  dsimp only
  classical
  let N := a.length
  let g := B * K
  let B' := B + g * R
  let A := integerTerms a
  let C := integerTerms (fillerBlock B g h N r H)
  let D := integerTerms (denseBlock B g R k)
  have hN0 : 0 < N := by omega
  have hk0 : 0 < k := by omega
  have hK0 : 0 < K := by omega
  have hg0 : 0 < g := Nat.mul_pos hB hK0
  have hB'0 : 0 < B' := by
    show 0 < B + g * R
    omega
  have hgn : h * N ≤ g := old_step_mul_le_new_step hN0 (Nat.le_of_dvd hK0 hdK) hb
  obtain ⟨hAC, hD⟩ := block_terms_disjoint ha hN0 hh hg0 hgn hH hR
  let f (i : ℕ) : ℤ := (fillerValue B g h N r H i : ℤ)
  have hfinj : Function.Injective f := by
    intro i j he
    apply (fillerValue_strictMono hN0 hh hgn (B := B) (r := r) (H := H)).injective
    change (fillerValue B g h N r H i : ℤ) = (fillerValue B g h N r H j : ℤ) at he
    exact_mod_cast he
  have hfi (i : ℕ) : Function.invFun f (f i) = i := Function.leftInverse_invFun hfinj i
  let row (x : ℤ) : ℤ := (rowIndex N r H (Function.invFun f x) : ℤ)
  let error (x : ℤ) : ℤ := (h : ℤ) * (rowOffset N r H (Function.invFun f x) : ℤ)
  have hCeq : C = (Finset.range r).image f := fillerTerms_eq_image _ _ _ _ _ _
  have hrow x (hx : x ∈ C) : x = (B : ℤ) + (B : ℤ) * K * row x + error x := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (hCeq ▸ hx)
    simp only [row, error, hfi]
    simp [f, fillerValue, g]
  have herr (x : ℤ) (_ : x ∈ C) : (h : ℤ) ∣ error x := dvd_mul_right _ _
  have hoffset : (∑ x ∈ C, |error x|) ≤ 3 * (h : ℤ) * (N : ℤ) ^ 2 := by
    rw [hCeq, Finset.sum_image (fun i _ j _ he => hfinj he)]
    have hs : (∑ i ∈ Finset.range r, |error (f i)|) =
        (h : ℤ) * (∑ i ∈ Finset.range r, (rowOffset N r H i : ℤ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp [error, hfi, abs_of_nonneg, mul_nonneg]
    rw [hs, ← Nat.cast_sum]
    calc
      _ ≤ (h : ℤ) * (3 * (N : ℤ) ^ 2) := mul_le_mul_of_nonneg_left
        (by exact_mod_cast rowOffset_sum_le (r := r) (H := H) hN) (Int.natCast_nonneg h)
      _ = _ := by ring
  have hbudget : mass A B + (∑ x ∈ C, |error x|) < (B : ℤ) * d := by
    have hhn := mul_nonneg (Int.natCast_nonneg h) (sq_nonneg (N : ℤ))
    nlinarith only [hoffset, hb, hhn]
  have hDense x (hx : x ∈ D) : (B : ℤ) * K ∣ x - B := by
    obtain ⟨y, hy, rfl⟩ := mem_integerTerms.mp hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy
    refine ⟨(R - k + j : ℕ), ?_⟩
    simp [denseValue, g]
  have hRef : (B : ℤ) * K ∣ (B' : ℤ) - B := by
    refine ⟨(R : ℤ), ?_⟩
    simp [B', g]
  have hi' : invariant ((A ∪ C) ∪ D) B' g K := by
    simpa [g] using invariant.advance_stage hi (by exact_mod_cast hB) (by exact_mod_cast hd)
      (by exact_mod_cast hdK) (by exact_mod_cast hdiv) hAC hD row error hrow herr hbudget hDense hRef
  have hACbounds (x : ℤ) (hx : x ∈ A ∪ C) : 0 ≤ x ∧ x ≤ B' := by
    have hmem : x ∈ integerTerms (extendPrefix a B g h N r H R k) := by
      simp only [extendPrefix, integerTerms_append]
      exact Finset.mem_union_left D hx
    obtain ⟨y, hy, rfl⟩ := mem_integerTerms.mp hmem
    refine ⟨Int.natCast_nonneg y, ?_⟩
    have hy' := extendPrefix_le_reference_sub_step ha hN0 hh hgn hH hR hkR hk0 hy
    exact_mod_cast (show y ≤ B' by
      show y ≤ B + g * R
      omega)
  have hDdist x (hx : x ∈ D) : |x - (B' : ℤ)| ≤ (g : ℤ) * k := by
    obtain ⟨y, hy, rfl⟩ := mem_integerTerms.mp hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
    have hj' := List.mem_range.mp hj
    have hx' : (denseValue B g R k j : ℤ) ≤ (B' : ℤ) := by
      have hle := denseValue_le_reference_sub_step (B := B) (g := g) hkR hj'
      exact_mod_cast (show denseValue B g R k j ≤ B' by
        show denseValue B g R k j ≤ B + g * R
        omega)
    rw [abs_of_nonpos (sub_nonpos.mpr hx')]
    have hkR' : (k : ℤ) ≤ R := by exact_mod_cast hkR
    have hj0 : 0 ≤ (j : ℤ) := Int.natCast_nonneg j
    have hg' : 0 ≤ (g : ℤ) := Int.natCast_nonneg g
    simp only [denseValue, B', Nat.cast_add, Nat.cast_mul, Nat.cast_sub hkR]
    nlinarith only [mul_nonneg hg' hj0]
  have hcap : 64 * g * k ^ 2 ≤ B' * K := by
    calc
      64 * g * k ^ 2 = (64 * B * k ^ 2) * K := by dsimp [g]; ring
      _ ≤ B' * K := Nat.mul_le_mul_right K hreference
  have hK' : 8 * (N + r) ≤ K := by omega
  have hACdist (x : ℤ) (hx : x ∈ A ∪ C) : |x - (B' : ℤ)| ≤ B' := by
    obtain ⟨hx0, hxB⟩ := hACbounds x hx
    rw [abs_of_nonpos (sub_nonpos.mpr hxB)]
    omega
  have hm' := next_mass_budget (A := A) (C := C) (D := D)
    (integerTerms_card_le a)
    (by simpa [C] using integerTerms_card_le (fillerBlock B g h N r H))
    (by simpa [D] using integerTerms_card_le (denseBlock B g R k))
    hD hACdist hDdist hK' hsize hcap (Nat.mul_pos hB'0 hK0)
  simpa [extendPrefix, A, C, D, B', g, N, add_assoc] using And.intro hi' hm'

end Jsp000726.Upper
