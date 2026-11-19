module

public import Mathlib.Combinatorics.Additive.SubsetSum
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Nat.Log
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Lean.Elab.Tactic.Omega

@[expose] public section

open Filter
open scoped BigOperators

namespace Jsp000726.PublicStructure

/-!
The dyadic inputs in this file match `Erdos587.CFP.exists_delta_dyadic_full_width` in
`plby/lean-proofs` at `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`, in
`src/latest/ErdosProblems/Erdos587/HooleyDyadicModel.lean`. The transport below treats that input as
an explicit hypothesis. The transport itself only imports Mathlib.
-/

private lemma dyadicScale_tendsto {b : ℕ} (hb : 0 < b) :
    Tendsto (fun N : ℕ => Nat.log (2 ^ (1000 * b)) N + 1) atTop atTop := by
  have hbase : 1 < (2 : ℕ) ^ (1000 * b) := Nat.one_lt_pow (by omega) (by omega)
  apply tendsto_atTop.mpr
  intro T
  filter_upwards [eventually_ge_atTop ((2 ^ (1000 * b)) ^ T)] with N hN
  exact (Nat.le_log_of_pow_le hbase hN).trans (Nat.le_add_right _ _)

private lemma dyadicScale_bounds {b N : ℕ} (hb : 0 < b) (hN : 0 < N)
    (hlog : 1 ≤ Nat.log (2 ^ (1000 * b)) N) :
    let t := Nat.log (2 ^ (1000 * b)) N + 1
    N ≤ 2 ^ (1000 * b * t) ∧ (2 ^ (20 * b * t) : ℕ) ^ 6 ≤ N := by
  let L := Nat.log (2 ^ (1000 * b)) N
  have hbase : 1 < (2 : ℕ) ^ (1000 * b) := Nat.one_lt_pow (by omega) (by omega)
  have hupper : N ≤ ((2 : ℕ) ^ (1000 * b)) ^ (L + 1) :=
    (Nat.lt_pow_succ_log_self hbase N).le
  have hlower : ((2 : ℕ) ^ (1000 * b)) ^ L ≤ N :=
    Nat.pow_log_le_self _ hN.ne'
  have hstep : 120 * (L + 1) ≤ 1000 * L := by change 1 ≤ L at hlog; omega
  have hstep' : (20 * b * (L + 1)) * 6 ≤ (1000 * b) * L := by
    calc
      (20 * b * (L + 1)) * 6 = b * ((20 * 6) * (L + 1)) := by ac_rfl
      _ ≤ b * (1000 * L) := Nat.mul_le_mul_left b hstep
      _ = (1000 * b) * L := by ac_rfl
  refine ⟨?_, ?_⟩
  · rw [← pow_mul] at hupper
    exact hupper
  · rw [← pow_mul]
    exact (Nat.pow_le_pow_right (by omega) hstep').trans (by simpa only [← pow_mul] using hlower)

/-- A dyadic subset-sum result in the indicated range also applies whenever the ambient integer
interval is bounded by the sixth power of the input cardinality. -/
theorem eventually_of_dyadic_sixth {R : Finset ℕ → Prop} {b : ℕ} (hb : 0 < b)
    (hdense : ∀ᶠ t : ℕ in atTop, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 (2 ^ (1000 * b * t)) → 2 ^ (20 * b * t) ≤ A.card → R A) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N → N ≤ A.card ^ 6 → R A := by
  have hscale := dyadicScale_tendsto hb
  filter_upwards [eventually_ge_atTop (1 : ℕ), hscale.eventually (eventually_ge_atTop 2),
    hscale.eventually hdense] with N hN hscale' ht
  intro A hA hcard
  obtain ⟨hupper, hlower⟩ := dyadicScale_bounds hb hN (by omega)
  apply ht A (hA.trans (Finset.Icc_subset_Icc le_rfl hupper))
  exact (Nat.pow_le_pow_iff_left (by decide : (6 : ℕ) ≠ 0)).mp (hlower.trans hcard)

/-- Integer-input version of `eventually_of_dyadic_sixth`. -/
theorem eventually_of_integer_dyadic_sixth {R : Finset ℤ → Prop} {b : ℕ} (hb : 0 < b)
    (hdense : ∀ᶠ t : ℕ in atTop, ∀ A : Finset ℤ,
      A ⊆ Finset.Icc 1 ((2 ^ (1000 * b * t) : ℕ) : ℤ) →
      2 ^ (20 * b * t) ≤ A.card → R A) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℤ,
      A ⊆ Finset.Icc 1 (N : ℤ) → N ≤ A.card ^ 6 → R A := by
  have hscale := dyadicScale_tendsto hb
  filter_upwards [eventually_ge_atTop (1 : ℕ), hscale.eventually (eventually_ge_atTop 2),
    hscale.eventually hdense] with N hN hscale' ht
  intro A hA hcard
  obtain ⟨hupper, hlower⟩ := dyadicScale_bounds hb hN (by omega)
  apply ht A (hA.trans (Finset.Icc_subset_Icc le_rfl (Int.ofNat_le.mpr hupper)))
  exact (Nat.pow_le_pow_iff_left (by decide : (6 : ℕ) ≠ 0)).mp (hlower.trans hcard)

/-- A finite affine box in the integers. A side of length `l` has `l + 1` points. -/
structure IntegerGAP where
  rank : ℕ
  base : ℤ
  step : Fin rank → ℤ
  length : Fin rank → ℕ

namespace IntegerGAP

abbrev Param (P : IntegerGAP) := (i : Fin P.rank) → Fin (P.length i + 1)

def eval (P : IntegerGAP) (x : P.Param) : ℤ :=
  P.base + ∑ i : Fin P.rank, (x i : ℤ) * P.step i

def carrier (P : IntegerGAP) : Finset ℤ :=
  (Finset.univ : Finset P.Param).image P.eval

def Proper (P : IntegerGAP) : Prop := Function.Injective P.eval

end IntegerGAP

/-- The part of the public dyadic GAP theorem consumed by the gap lower bound. -/
def DyadicSubsetStructure : Prop :=
  ∃ b R D F : ℕ, 0 < b ∧ 0 < R ∧ 0 < D ∧ 0 < F ∧
    ∀ᶠ t : ℕ in atTop, ∀ A : Finset ℤ,
      A ⊆ Finset.Icc 1 ((2 ^ (1000 * b * t) : ℕ) : ℤ) →
      2 ^ (20 * b * t) ≤ A.card →
      ∃ m : ℕ, 0 < m ∧ A.card ≤ R * m ∧ ∃ P : IntegerGAP,
        0 < P.rank ∧ P.rank ≤ D ∧ P.Proper ∧ P.carrier ⊆ A.subsetSum ∧
        (∀ i, m ≤ F * P.length i) ∧ m ^ (P.rank + 1) ≤ 2 * F ^ P.rank * P.carrier.card

/-- A progression in the subset sums of a set with ambient range at most its cardinality to
the sixth power. The rank and both losses are uniform in the input interval and the set. -/
def PowerSubsetStructure : Prop :=
  ∃ D C : ℕ, 0 < D ∧ 0 < C ∧
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℤ, A ⊆ Finset.Icc 1 (N : ℤ) → N ≤ A.card ^ 6 →
      ∃ P : IntegerGAP, 0 < P.rank ∧ P.rank ≤ D ∧ P.Proper ∧ P.carrier ⊆ A.subsetSum ∧
        (∀ i, A.card ≤ C * P.length i) ∧ A.card ^ (P.rank + 1) ≤ C * P.carrier.card

theorem powerSubsetStructure_of_dyadic (h : DyadicSubsetStructure) : PowerSubsetStructure := by
  obtain ⟨b, R, D, F, hb, hR, hD, hF, hdyadic⟩ := h
  let C := max (R * F) (R ^ (D + 1) * (2 * F ^ D))
  have hC : 0 < C := (Nat.mul_pos hR hF).trans_le (le_max_left _ _)
  refine ⟨D, C, hD, hC, ?_⟩
  filter_upwards [eventually_of_integer_dyadic_sixth hb hdyadic] with N hN
  intro A hA hsize
  obtain ⟨m, _, hretain, P, hr, hrD, hproper, hsub, hlength, hcard⟩ := hN A hA hsize
  refine ⟨P, hr, hrD, hproper, hsub, ?_, ?_⟩
  · intro i
    calc
      A.card ≤ R * m := hretain
      _ ≤ R * (F * P.length i) := Nat.mul_le_mul_left _ (hlength i)
      _ = (R * F) * P.length i := (Nat.mul_assoc _ _ _).symm
      _ ≤ C * P.length i := Nat.mul_le_mul_right _ (le_max_left _ _)
  · have hRp : R ^ (P.rank + 1) ≤ R ^ (D + 1) :=
      Nat.pow_le_pow_right hR (Nat.add_le_add_right hrD 1)
    have hFp : F ^ P.rank ≤ F ^ D := Nat.pow_le_pow_right hF hrD
    calc
      A.card ^ (P.rank + 1) ≤ (R * m) ^ (P.rank + 1) :=
        Nat.pow_le_pow_left hretain _
      _ = R ^ (P.rank + 1) * m ^ (P.rank + 1) := mul_pow _ _ _
      _ ≤ R ^ (D + 1) * (2 * F ^ P.rank * P.carrier.card) := Nat.mul_le_mul hRp hcard
      _ ≤ R ^ (D + 1) * (2 * F ^ D * P.carrier.card) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hFp))
      _ = (R ^ (D + 1) * (2 * F ^ D)) * P.carrier.card := (Nat.mul_assoc _ _ _).symm
      _ ≤ C * P.carrier.card := Nat.mul_le_mul_right _ (le_max_right _ _)

end Jsp000726.PublicStructure
