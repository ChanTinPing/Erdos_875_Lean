module

public import Jsp000726.LowerAsymptoticsRanks
public import Jsp000726.LowerProgressions
public import Jsp000726.LowerRankTwoDichotomy
public import Jsp000726.LowerRankTwoInput

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726

open Finset PublicStructure

/-- The numeric carrier and the rank-two spacing dichotomy for a structural
witness on opposite pairs. In the short case the ordinary progression projects
from a longest chain inside the same rank-two carrier. -/
theorem opposite_rankTwo_carrier {a : ℕ → ℕ} {n C : ℕ} {P : IntegerGAP}
    (hn : 16 ≤ n) (hr : P.rank = 2) (h : OppositeLayerWitness a n C P) :
    let q := n / 2
    let m := n / 16
    let T := univ.map (oppositeLow q m) ∪ univ.map (oppositeHigh q m)
    ∃ (Q : Finset ℕ) (b V : ℕ), Q.card = P.carrier.card ∧ Q ⊆ sumLayer a T m ∧
      b ∈ Q ∧ b + V ∈ Q ∧ 0 < V ∧ (∀ x ∈ Q, b ≤ x ∧ x ≤ b + V) ∧
      let R := (V : ℝ) / (Q.card : ℝ)
      ((∀ x ∈ Q, ∀ y ∈ Q, x < y → (x : ℝ) + R / 10 < (y : ℝ)) ∨
        ∃ d L B : ℕ, 0 < d ∧ (d : ℝ) ≤ R / 10 ∧ 2 ≤ L ∧
          ProgressionInLayer a T m B d L ∧ d * (L - 1) ≤ V ∧
          (∀ x ∈ Q, ∀ y ∈ Q, x < y → x + d ≤ y) ∧
          ∀ H : ℝ, 0 ≤ H → H < (7 / 40 : ℝ) * R * (L : ℝ) → ∀ z : ℕ,
            (Q.filter fun x => x ≤ z ∧ z < x + (⌊H⌋₊ + 1)).card ≤ L) := by
  intro q m T
  obtain ⟨hproper, hwidth, _, htrans⟩ := h
  have hm : 0 < m := by dsimp [m]; omega
  have hw i : 0 < P.length i := by
    by_contra! hz
    have hi := hwidth i
    rw [Nat.eq_zero_of_le_zero hz, Nat.mul_zero] at hi
    omega
  obtain ⟨g₁, g₂, X, Y, hX, hY, hcarrier, hInject, hvolume⟩ :=
    rankTwo_integerGAP_as_nontrivial_box P hr hproper hw
  let S := Icc (0 : ℤ) (X : ℤ) ×ˢ Icc (0 : ℤ) (Y : ℤ)
  let f (p : ℤ × ℤ) := P.base + g₁ * p.1 + g₂ * p.2
  let offset : ℤ := (∑ i : Fin m, a (oppositeLow q m i) : ℕ)
  let F (p : ℤ × ℤ) := (offset + f p).toNat
  let Q := S.image F
  have hpoint {p : ℤ × ℤ} (hp : p ∈ S) :
      (F p : ℤ) = offset + f p ∧ F p ∈ sumLayer a T m := by
    have hx : f p ∈ P.carrier := hcarrier ▸ mem_image.mpr ⟨p, hp, rfl⟩
    obtain ⟨k, hk, he⟩ := mem_map.mp (htrans _ hx)
    change (k : ℤ) = offset + f p at he
    have hf : F p = k := by unfold F; rw [← he, Int.toNat_natCast]
    exact ⟨by rw [hf, he], hf.symm ▸ hk⟩
  have hFInject : Set.InjOn F S := by
    intro p hp p' hp' hh
    apply hInject hp hp'
    have hdiff := congrArg (fun z : ℕ => (z : ℤ)) hh
    rw [(hpoint hp).1, (hpoint hp').1] at hdiff
    change f p = f p'
    exact add_left_cancel hdiff
  have hCard : Q.card = P.carrier.card := by
    rw [hcarrier]
    exact (card_image_of_injOn hFInject).trans (card_image_of_injOn hInject).symm
  have hSub : Q ⊆ sumLayer a T m := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hk
    exact (hpoint hp).2
  have box (p : ℤ × ℤ) : p ∈ S ↔ 0 ≤ p.1 ∧ p.1 ≤ (X : ℤ) ∧ 0 ≤ p.2 ∧ p.2 ≤ (Y : ℤ) := by
    simp only [S, mem_product, mem_Icc, and_assoc]
  obtain ⟨lo, hi, hspan, ⟨xlo, ylo, hxl, hxu, hyl, hyu, hlo⟩,
      ⟨xhi, yhi, hxl', hxu', hyl', hyu', hhi⟩, hVwidth⟩ :=
    rankTwo_box_span (offset + P.base) g₁ g₂ X Y
  have hplo : (xlo, ylo) ∈ S := (box _).2 ⟨hxl, hxu, hyl, hyu⟩
  have hphi : (xhi, yhi) ∈ S := (box _).2 ⟨hxl', hxu', hyl', hyu'⟩
  have hlo' : (F (xlo, ylo) : ℤ) = lo := by
    rw [(hpoint hplo).1]
    change offset + (P.base + g₁ * xlo + g₂ * ylo) = lo
    linarith only [hlo]
  have hhi' : (F (xhi, yhi) : ℤ) = hi := by
    rw [(hpoint hphi).1]
    change offset + (P.base + g₁ * xhi + g₂ * yhi) = hi
    linarith only [hhi]
  have hlohi : lo ≤ hi := by
    rw [← hlo]
    exact (hspan _ _ hxl hxu hyl hyu).2
  let b := lo.toNat
  let V := (hi - lo).toNat
  have hBint : (b : ℤ) = lo := by
    apply Int.toNat_of_nonneg
    rw [← hlo']
    exact Int.natCast_nonneg _
  have hVint : (V : ℤ) = hi - lo := Int.toNat_of_nonneg (sub_nonneg.mpr hlohi)
  have hb : b ∈ Q := mem_image.mpr ⟨(xlo, ylo), hplo, Int.ofNat_inj.mp (hlo'.trans hBint.symm)⟩
  have hbV : b + V ∈ Q := by
    refine mem_image.mpr ⟨(xhi, yhi), hphi, Int.ofNat_inj.mp ?_⟩
    rw [Nat.cast_add, hBint, hVint, hhi']
    omega
  have hSpan : ∀ k ∈ Q, b ≤ k ∧ k ≤ b + V := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hk
    obtain ⟨hx0, hx1, hy0, hy1⟩ := (box p).1 hp
    have hh := hspan p.1 p.2 hx0 hx1 hy0 hy1
    have hv : (F p : ℤ) = (offset + P.base) + g₁ * p.1 + g₂ * p.2 := by
      rw [(hpoint hp).1]
      dsimp [f]
      ring
    constructor
    · apply Int.ofNat_le.mp
      rw [hBint, hv]
      exact hh.1
    · apply Int.ofNat_le.mp
      rw [Nat.cast_add, hBint, hVint, hv]
      omega
  have hVol : Q.card = (X + 1) * (Y + 1) := hCard.trans hvolume
  have hCardFour : 4 ≤ Q.card := by
    rw [hVol]
    exact Nat.mul_le_mul (by omega : 2 ≤ X + 1) (by omega : 2 ≤ Y + 1)
  have hV : 0 < V := by
    by_contra! h
    have hv0 : V = 0 := by omega
    have hCard := (card_le_one (s := Q)).mpr fun x hx y hy => by
      obtain ⟨hxl, hxu⟩ := hSpan x hx
      obtain ⟨hyl, hyu⟩ := hSpan y hy
      omega
    omega
  let R := (V : ℝ) / (Q.card : ℝ)
  have hR : 0 < R := div_pos (by exact_mod_cast hV) (by exact_mod_cast (by omega : 0 < Q.card))
  have hVreal : (V : ℝ) = |(g₁ : ℝ)| * (X : ℝ) + |(g₂ : ℝ)| * (Y : ℝ) := by
    exact_mod_cast hVint.trans hVwidth
  have hVolReal : (Q.card : ℝ) = ((X : ℝ) + 1) * ((Y : ℝ) + 1) := by exact_mod_cast hVol
  have hRvol : |(g₁ : ℝ)| * (X : ℝ) + |(g₂ : ℝ)| * (Y : ℝ) =
      R * ((X : ℝ) + 1) * ((Y : ℝ) + 1) := by
    rw [← hVreal, mul_assoc, ← hVolReal]
    exact (div_mul_cancel₀ _ (by exact_mod_cast (by omega : Q.card ≠ 0))).symm
  refine ⟨Q, b, V, hCard, hSub, hb, hbV, hV, hSpan, ?_⟩
  have difference {p p' : ℤ × ℤ} (hp : p ∈ S) (hp' : p' ∈ S) :
      ((F p' : ℤ) - (F p : ℤ)) = g₁ * (p'.1 - p.1) + g₂ * (p'.2 - p.2) := by
    rw [(hpoint hp).1, (hpoint hp').1]
    dsimp [f]
    ring
  have diffBox {p p' : ℤ × ℤ} (hp : p ∈ S) (hp' : p' ∈ S) :
      |p'.1 - p.1| ≤ (X : ℤ) ∧ |p'.2 - p.2| ≤ (Y : ℤ) := by
    obtain ⟨hx, hx', hy, hy'⟩ := (box p).1 hp
    obtain ⟨hx₂, hx₂', hy₂, hy₂'⟩ := (box p').1 hp'
    exact ⟨abs_le.mpr ⟨by omega, by omega⟩, abs_le.mpr ⟨by omega, by omega⟩⟩
  have orderedDifference {p p' : ℤ × ℤ} (hp : p ∈ S) (hp' : p' ∈ S) (hF : F p < F p') :
      (p'.1 - p.1 ≠ 0 ∨ p'.2 - p.2 ≠ 0) ∧
        (p'.1 - p.1).natAbs ≤ X ∧ (p'.2 - p.2).natAbs ≤ Y ∧
        |g₁ * (p'.1 - p.1) + g₂ * (p'.2 - p.2)| = (F p' : ℤ) - (F p : ℤ) := by
    have hpos : (F p : ℤ) < (F p' : ℤ) := Int.ofNat_lt.mpr hF
    have he := difference hp hp'
    have hz : p'.1 - p.1 ≠ 0 ∨ p'.2 - p.2 ≠ 0 := by
      by_contra! hh
      rw [hh.1, hh.2, mul_zero, mul_zero, add_zero] at he
      omega
    obtain ⟨hx, hy⟩ := diffBox hp hp'
    refine ⟨hz, Int.ofNat_le.mp (by rwa [Int.natCast_natAbs]),
      Int.ofNat_le.mp (by rwa [Int.natCast_natAbs]), ?_⟩
    rw [← he, abs_of_nonneg (sub_nonneg.mpr hpos.le)]
  rcases rankTwo_box_dichotomy hR hX hY hRvol hInject with
    hno | ⟨x, y, hxy, hx, hy, hBez, hDpos, hDhi, hcap, hSpacing, hSep⟩
  · left
    intro u hu v hv huv
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hu
    obtain ⟨p', hp', rfl⟩ := mem_image.mp hv
    obtain ⟨hd, hdx, hdy, he⟩ := orderedDifference hp hp' huv
    have hh := hno _ _ hd hdx hdy
    rw [he, Int.cast_sub, Int.cast_natCast, Int.cast_natCast] at hh
    linarith
  · right
    let d := |g₁ * x + g₂ * y|.toNat
    let L := chainCapacity x y (X + 1) (Y + 1) + 1
    have hD : (d : ℤ) = |g₁ * x + g₂ * y| := Int.toNat_of_nonneg (abs_nonneg _)
    have hd : 0 < d := Int.ofNat_lt.mp (by rwa [hD])
    have hdR : (d : ℝ) ≤ R / 10 := by exact_mod_cast (hD ▸ hDhi)
    have hL : 2 ≤ L := by dsimp [L]; omega
    obtain ⟨c, hc⟩ := full_box_chain_abs (Nat.succ_pos X) (Nat.succ_pos Y) hxy g₁ g₂
    let B := (offset + P.base + c).toNat
    have chain (j : ℕ) (hj : j < L) :
        ∃ p ∈ S, (F p : ℤ) = offset + P.base + c + (j : ℤ) * (d : ℤ) := by
      have hj' : j ≤ chainCapacity x y (X + 1) (Y + 1) := Nat.lt_succ_iff.mp hj
      obtain ⟨u, v, hu, hu', hv, hv', he⟩ := hc j hj' 
      have hp : (u, v) ∈ S := (box _).2 ⟨hu, by push_cast at hu'; omega, hv, by push_cast at hv'; omega⟩
      refine ⟨(u, v), hp, ?_⟩
      rw [(hpoint hp).1, hD]
      change offset + (P.base + g₁ * u + g₂ * v) =
        offset + P.base + c + (j : ℤ) * |g₁ * x + g₂ * y|
      linarith only [he]
    have hB : (B : ℤ) = offset + P.base + c := by
      apply Int.toNat_of_nonneg
      obtain ⟨p, hp, hp'⟩ := chain 0 (by omega)
      have hpos := Int.natCast_nonneg (F p)
      simp only [Nat.cast_zero, zero_mul, add_zero] at hp'
      omega
    have hProg (j : ℕ) (hj : j < L) : B + d * j ∈ Q := by
      obtain ⟨p, hp, hp'⟩ := chain j hj
      refine mem_image.mpr ⟨p, hp, Int.ofNat_inj.mp ?_⟩
      rw [Nat.cast_add, Nat.cast_mul, hB, hp', mul_comm (d : ℤ)]
    have hProgLayer : ProgressionInLayer a T m B d L := by
      intro j hj
      exact mem_sumLayer.mp (hSub (hProg j hj))
    have hProgSpan : d * (L - 1) ≤ V := by
      have hlo := (hSpan _ (hProg 0 (by omega))).1
      have hhi := (hSpan _ (hProg (L - 1) (by omega))).2
      omega
    refine ⟨d, L, B, hd, hdR, hL, hProgLayer, hProgSpan, ?_, ?_⟩
    · intro u hu v hv huv
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hu
      obtain ⟨p', hp', rfl⟩ := mem_image.mp hv
      obtain ⟨hh, hdx, hdy, he⟩ := orderedDifference hp hp' huv
      have hDist := hSpacing _ _ hh hdx hdy
      rw [← hD, he] at hDist
      omega
    · intro H hH hHhi z
      apply projected_box_window_card_le_of_real_separation (Nat.succ_pos X) (Nat.succ_pos Y)
        hxy hBez S F hH _ _ z
      · intro p hp
        obtain ⟨h₁, h₂, h₃, h₄⟩ := (box p).1 hp
        push_cast
        omega
      · intro p hp p' hp' hlabel
        obtain ⟨h₁, h₂⟩ := diffBox hp' hp
        have hh := hSep p.1 p.2 p'.1 p'.2 h₁ h₂ hlabel
        have he : (F p : ℤ) - (F p' : ℤ) =
            (g₁ * p.1 + g₂ * p.2) - (g₁ * p'.1 + g₂ * p'.2) := by
          rw [difference hp' hp]
          ring
        rw [← he] at hh
        exact hHhi.trans_le (by exact_mod_cast hh)

end Jsp000726
