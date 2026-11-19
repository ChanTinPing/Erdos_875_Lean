module

public import Jsp000726.LowerRankTwo
public import Jsp000726.LowerRankTwoWindow
public import Jsp000726.LowerRankTwoCapacity
public import Jsp000726.LowerRankTwoGeometry
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726

/-- Proper affine projections cannot annihilate any nonzero coordinate difference
that fits inside their box. -/
theorem proper_box_direction_ne_zero {X Y : ℕ} {base g₁ g₂ a b : ℤ}
    (hproper : Set.InjOn (fun p : ℤ × ℤ => base + g₁ * p.1 + g₂ * p.2)
      ((Finset.Icc (0 : ℤ) (X : ℤ) ×ˢ Finset.Icc (0 : ℤ) (Y : ℤ) : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)))
    (hnonzero : a ≠ 0 ∨ b ≠ 0) (ha : a.natAbs ≤ X) (hb : b.natAbs ≤ Y) :
    g₁ * a + g₂ * b ≠ 0 := by
  have side (z : ℤ) (N : ℕ) (hz : z.natAbs ≤ N) :
      max 0 z ∈ Finset.Icc (0 : ℤ) (N : ℤ) ∧ max 0 (-z) ∈ Finset.Icc (0 : ℤ) (N : ℤ) := by
    have h : |z| ≤ (N : ℤ) := by rw [← Int.natCast_natAbs]; exact Int.ofNat_le.mpr hz
    have h' := abs_le.mp h
    exact ⟨Finset.mem_Icc.mpr ⟨le_max_left _ _, max_le (Int.natCast_nonneg _) h'.2⟩,
      Finset.mem_Icc.mpr ⟨le_max_left _ _, max_le (Int.natCast_nonneg _) (by omega)⟩⟩
  have split (z : ℤ) : max 0 z - max 0 (-z) = z := by omega
  let P := (max 0 a, max 0 b)
  let Q := (max 0 (-a), max 0 (-b))
  have hP : P ∈ (Finset.Icc (0 : ℤ) (X : ℤ) ×ˢ Finset.Icc (0 : ℤ) (Y : ℤ)) :=
    Finset.mem_product.mpr ⟨(side a X ha).1, (side b Y hb).1⟩
  have hQ : Q ∈ (Finset.Icc (0 : ℤ) (X : ℤ) ×ˢ Finset.Icc (0 : ℤ) (Y : ℤ)) :=
    Finset.mem_product.mpr ⟨(side a X ha).2, (side b Y hb).2⟩
  intro hzero
  have hvalues : base + g₁ * P.1 + g₂ * P.2 = base + g₁ * Q.1 + g₂ * Q.2 := by
    apply sub_eq_zero.mp
    calc
      _ = g₁ * (max 0 a - max 0 (-a)) + g₂ * (max 0 b - max 0 (-b)) := by dsimp [P, Q]; ring
      _ = 0 := by rw [split, split, hzero]
  have hsame := hproper hP hQ hvalues
  have hfst : max 0 a = max 0 (-a) := congrArg Prod.fst hsame
  have hsnd : max 0 b = max 0 (-b) := congrArg Prod.snd hsame
  exact hnonzero.elim (fun h => h (by omega : a = 0)) (fun h => h (by omega : b = 0))

/-- At least one generator is large compared to the mean spacing times the
opposite side length. -/
theorem rankTwo_generator_large {R X Y g₁ g₂ : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hspan : |g₁| * X + |g₂| * Y = R * (X + 1) * (Y + 1)) :
    R * (Y + 1) ≤ 2 * |g₁| ∨ R * (X + 1) ≤ 2 * |g₂| := by
  by_contra! h
  have h1 := mul_lt_mul_of_pos_right h.1 (show 0 < X + 1 by linarith)
  have h2 := mul_lt_mul_of_pos_right h.2 (show 0 < Y + 1 by linarith)
  have h3 := add_lt_add h1 h2
  nlinarith only [h3, hspan, abs_nonneg g₁, abs_nonneg g₂]

/-- A short coordinate difference can be taken primitive. Its projected length
then bounds the distance of every nonzero projected difference in the box. -/
theorem rankTwo_short_primitive_spacing {X Y : ℕ} {R : ℝ} {base g₁ g₂ : ℤ}
    (hR : 0 < R)
    (hspan : |(g₁ : ℝ)| * (X : ℝ) + |(g₂ : ℝ)| * (Y : ℝ) =
      R * ((X : ℝ) + 1) * ((Y : ℝ) + 1))
    (hproper : Set.InjOn (fun p : ℤ × ℤ => base + g₁ * p.1 + g₂ * p.2)
      ((Finset.Icc (0 : ℤ) (X : ℤ) ×ˢ Finset.Icc (0 : ℤ) (Y : ℤ) : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)))
    {a b : ℤ} (hab : a ≠ 0 ∨ b ≠ 0) (ha : a.natAbs ≤ X) (hb : b.natAbs ≤ Y)
    (hshort : ((|g₁ * a + g₂ * b| : ℤ) : ℝ) ≤ R / 10) :
    ∃ x y : ℤ, (x ≠ 0 ∨ y ≠ 0) ∧ x.natAbs ≤ X ∧ y.natAbs ≤ Y ∧
      (∃ u v : ℤ, u * x + v * y = 1) ∧
      0 < |g₁ * x + g₂ * y| ∧ ((|g₁ * x + g₂ * y| : ℤ) : ℝ) ≤ R / 10 ∧
      ∀ s t : ℤ, (s ≠ 0 ∨ t ≠ 0) → s.natAbs ≤ X → t.natAbs ≤ Y →
        |g₁ * x + g₂ * y| ≤ |g₁ * s + g₂ * t| := by
  obtain ⟨k, x, y, hk, hax, hby, hbez, hxa, hyb, hproj⟩ :=
    exists_primitive_int_direction hab g₁ g₂
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_contra! hh
    obtain ⟨u, v, huv⟩ := hbez
    simp [hh.1, hh.2] at huv
  have hNat : ∀ z w : ℤ, |z| ≤ |w| → z.natAbs ≤ w.natAbs := by
    intro z w h
    apply Int.ofNat_le.mp
    simpa only [Int.natCast_natAbs] using h
  have hx : x.natAbs ≤ X := (hNat _ _ hxa).trans ha
  have hy : y.natAbs ≤ Y := (hNat _ _ hyb).trans hb
  have hpos : 0 < |g₁ * x + g₂ * y| := abs_pos.mpr (proper_box_direction_ne_zero hproper hxy hx hy)
  have hsz : ((|g₁ * x + g₂ * y| : ℤ) : ℝ) ≤ R / 10 :=
    ((Int.cast_le (R := ℝ)).2 hproj).trans hshort
  refine ⟨x, y, hxy, hx, hy, hbez, hpos, hsz, ?_⟩
  intro s t hst hs ht
  by_cases hshort' : ((|g₁ * s + g₂ * t| : ℤ) : ℝ) ≤ R / 10
  · have bnd {z : ℤ} {N : ℕ} (hz : z.natAbs ≤ N) : |(z : ℝ)| ≤ (N : ℝ) + 1 := by
      have hi : |z| ≤ (N : ℤ) := by rw [← Int.natCast_natAbs]; exact Int.ofNat_le.mpr hz
      have hr : |(z : ℝ)| ≤ (N : ℝ) := by exact_mod_cast hi
      linarith
    have hszR : |(g₁ : ℝ) * (x : ℝ) + (g₂ : ℝ) * (y : ℝ)| ≤ R / 10 := by
      exact_mod_cast hsz
    have hshortR : |(g₁ : ℝ) * (s : ℝ) + (g₂ : ℝ) * (t : ℝ)| ≤ R / 10 := by
      exact_mod_cast hshort'
    have hdet : (x : ℝ) * (t : ℝ) - (y : ℝ) * (s : ℝ) = 0 :=
      short_directions_parallel hR (by positivity) (by positivity)
        (rankTwo_generator_large (Nat.cast_nonneg X) (Nat.cast_nonneg Y) hspan)
        (bnd hx) (bnd hs) (bnd hy) (bnd ht) hszR hshortR (by
          intro hn
          have hni : x * t - y * s ≠ 0 := by exact_mod_cast hn
          exact_mod_cast Int.one_le_abs hni)
    have hdetI : x * t - y * s = 0 := by exact_mod_cast hdet
    exact int_collinear_spacing hbez (sub_eq_zero.mp hdetI)
      (proper_box_direction_ne_zero hproper hst hs ht)
  · exact (Int.cast_le (R := ℝ)).mp (hsz.trans (le_of_not_ge hshort'))

private theorem rankTwo_separation_first_binding {X Y : ℕ} {R : ℝ}
    {g₁ g₂ x y a b a' b' : ℤ} (hR : 0 ≤ R) (hY : 0 < Y) (hx : x ≠ 0)
    (hxb : x.natAbs ≤ X)
    (hbind : |(y : ℝ)| * ((X : ℝ) / |(x : ℝ)|) ≤ (Y : ℝ))
    (hspan : |(g₁ : ℝ)| * (X : ℝ) + |(g₂ : ℝ)| * (Y : ℝ) =
      R * ((X : ℝ) + 1) * ((Y : ℝ) + 1))
    (hshort : ((|g₁ * x + g₂ * y| : ℤ) : ℝ) ≤ R / 10)
    (hcoords : |a - a'| ≤ (X : ℤ))
    (hlabel : x * b - y * a ≠ x * b' - y * a') :
    (7 / 40 : ℝ) * R * ((chainCapacity x y (X + 1) (Y + 1) : ℝ) + 1) ≤
      ((|(g₁ * a + g₂ * b) - (g₁ * a' + g₂ * b')| : ℤ) : ℝ) := by
  let q := chainCapacity x y (X + 1) (Y + 1)
  let scale := (X : ℝ) / |(x : ℝ)|
  let M := ((X : ℝ) + 1) * ((Y : ℝ) + 1)
  have hxR : (x : ℝ) ≠ 0 := by exact_mod_cast hx
  have hxpos : 0 < |(x : ℝ)| := abs_pos.mpr hxR
  have hXeq : |(x : ℝ)| * scale = (X : ℝ) := by
    unfold scale
    rw [mul_comm, div_mul_cancel₀ _ hxpos.ne']
  have hx1 : (1 : ℝ) ≤ |(x : ℝ)| := by exact_mod_cast Int.one_le_abs hx
  have hxXint : |x| ≤ (X : ℤ) := by rw [← Int.natCast_natAbs]; exact Int.ofNat_le.mpr hxb
  have hxX : |(x : ℝ)| ≤ (X : ℝ) := by exact_mod_cast hxXint
  have hscale1 : 1 ≤ scale := (le_div_iff₀ hxpos).2 (by simpa only [one_mul] using hxX)
  have hscaleX : scale ≤ (X : ℝ) := div_le_self (Nat.cast_nonneg X) hx1
  have hscaleM : scale ≤ M := by
    unfold M
    have hh := mul_le_mul_of_nonneg_right (show (X : ℝ) ≤ (X : ℝ) + 1 by linarith)
      (show 0 ≤ (Y : ℝ) + 1 by positivity)
    have hk := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ (Y : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) Y])
      (Nat.cast_nonneg X : (0 : ℝ) ≤ (X : ℝ))
    calc
      _ ≤ (X : ℝ) := hscaleX
      _ ≤ (X : ℝ) * ((Y : ℝ) + 1) := by simpa only [mul_one] using hk
      _ ≤ _ := hh
  have hXY : (X : ℝ) * (Y : ℝ) ≤ M := by
    unfold M
    exact mul_le_mul (by linarith) (by linarith) (Nat.cast_nonneg Y) (by positivity)
  have hshortR : |(x : ℝ) * (g₁ : ℝ) + (y : ℝ) * (g₂ : ℝ)| ≤ R / 10 := by
    have hh : |(g₁ : ℝ) * (x : ℝ) + (g₂ : ℝ) * (y : ℝ)| ≤ R / 10 := by exact_mod_cast hshort
    simpa only [mul_comm] using hh
  have gen := rankTwo_long_generator_lower_bound hR (Nat.cast_pos.mpr hY)
    (zero_le_one.trans hscale1) hxR hXeq hbind hXY hscaleM (by simpa only [M, mul_assoc] using hspan)
    hshortR
  let k := x * b - y * a
  let l := x * b' - y * a'
  have hl : ((k - l : ℤ) : ℝ) = (x : ℝ) * ((b : ℝ) - (b' : ℝ)) -
      (y : ℝ) * ((a : ℝ) - (a' : ℝ)) := by
    simp only [k, l, Int.cast_sub, Int.cast_mul]
    ring
  have hc : |(a : ℝ) - (a' : ℝ)| ≤ (X : ℝ) := by exact_mod_cast hcoords
  have hseparation := rankTwo_chain_value_separation hxR (zero_le_one.trans hscale1)
    hXeq (show k ≠ l from hlabel) hl gen hshortR hc
  have hq : (q : ℝ) ≤ scale := by
    have hh := chainCapacity_binding_scale (x := x) (y := y)
      (Nat.succ_pos X) (Nat.succ_pos Y) hx (by simpa only [Nat.succ_sub_one] using hbind)
    simpa only [Nat.succ_sub_one] using hh.1
  have hout := rounded_chain_separation hR hscale1
    (add_le_add_left hq (1 : ℝ)) hseparation
  simpa only [q, Int.cast_abs, Int.cast_add, Int.cast_sub, Int.cast_mul] using hout

private theorem chainCapacity_swap (x y : ℤ) (X Y : ℕ) (hxy : x ≠ 0 ∨ y ≠ 0) :
    chainCapacity x y (X + 1) (Y + 1) = chainCapacity y x (Y + 1) (X + 1) := by
  have h₁ (t : ℕ) := le_chainCapacity_iff (x := x) (y := y) (t := t)
    (Nat.succ_pos X) (Nat.succ_pos Y) hxy
  have h₂ (t : ℕ) := le_chainCapacity_iff (x := y) (y := x) (t := t)
    (Nat.succ_pos Y) (Nat.succ_pos X) hxy.symm
  apply le_antisymm
  · exact (h₂ _).2 ((h₁ _).1 le_rfl).symm
  · exact (h₁ _).2 ((h₂ _).1 le_rfl).symm

/-- Distinct primitive chains are separated by a fixed multiple of the mean
spacing times the exact integer chain length. -/
theorem rankTwo_projected_chain_separation {X Y : ℕ} {R : ℝ}
    {g₁ g₂ x y a b a' b' : ℤ}
    (hR : 0 ≤ R) (hX : 0 < X) (hY : 0 < Y)
    (hxy : x ≠ 0 ∨ y ≠ 0) (hx : x.natAbs ≤ X) (hy : y.natAbs ≤ Y)
    (hspan : |(g₁ : ℝ)| * (X : ℝ) + |(g₂ : ℝ)| * (Y : ℝ) =
      R * ((X : ℝ) + 1) * ((Y : ℝ) + 1))
    (hshort : ((|g₁ * x + g₂ * y| : ℤ) : ℝ) ≤ R / 10)
    (ha : |a - a'| ≤ (X : ℤ)) (hb : |b - b'| ≤ (Y : ℤ))
    (hl : x * b - y * a ≠ x * b' - y * a') :
    (7 / 40 : ℝ) * R * ((chainCapacity x y (X + 1) (Y + 1) : ℝ) + 1) ≤
      ((|(g₁ * a + g₂ * b) - (g₁ * a' + g₂ * b')| : ℤ) : ℝ) := by
  have hxyR : (x : ℝ) ≠ 0 ∨ (y : ℝ) ≠ 0 :=
    hxy.imp (fun h => by exact_mod_cast h) (fun h => by exact_mod_cast h)
  rcases rankTwo_binding_side (Nat.cast_nonneg X) (Nat.cast_nonneg Y) hxyR with
    ⟨hxR, hbind⟩ | ⟨hyR, hbind⟩
  · exact rankTwo_separation_first_binding hR hY (by exact_mod_cast hxR)
      hx hbind hspan hshort ha hl
  · have hspan' : |(g₂ : ℝ)| * (Y : ℝ) + |(g₁ : ℝ)| * (X : ℝ) =
        R * ((Y : ℝ) + 1) * ((X : ℝ) + 1) := by
      calc
        _ = |(g₁ : ℝ)| * (X : ℝ) + |(g₂ : ℝ)| * (Y : ℝ) := add_comm _ _
        _ = _ := by rw [hspan]; ring
    have hshort' : ((|g₂ * y + g₁ * x| : ℤ) : ℝ) ≤ R / 10 :=
      (by simpa only [add_comm] using hshort)
    have hl' : y * a - x * b ≠ y * a' - x * b' := by
      intro he
      apply hl
      omega
    have hsep := rankTwo_separation_first_binding hR hX (by exact_mod_cast hyR)
      hy hbind hspan' hshort' hb hl'
    simpa only [chainCapacity_swap x y X Y hxy, add_comm (g₂ * b) (g₁ * a),
      add_comm (g₂ * b') (g₁ * a')] using hsep

/-- A proper rank-two box either has no short projected difference, or has a
primitive chain direction with the required minimum spacing and inter-chain
separation. The native integer chain length is used in the separation bound. -/
theorem rankTwo_box_dichotomy {X Y : ℕ} {R : ℝ} {base g₁ g₂ : ℤ}
    (hR : 0 < R) (hX : 0 < X) (hY : 0 < Y)
    (hspan : |(g₁ : ℝ)| * (X : ℝ) + |(g₂ : ℝ)| * (Y : ℝ) =
      R * ((X : ℝ) + 1) * ((Y : ℝ) + 1))
    (hproper : Set.InjOn (fun p : ℤ × ℤ => base + g₁ * p.1 + g₂ * p.2)
      ((Finset.Icc (0 : ℤ) (X : ℤ) ×ˢ Finset.Icc (0 : ℤ) (Y : ℤ) : Finset (ℤ × ℤ)) : Set (ℤ × ℤ))) :
    (∀ a b : ℤ, (a ≠ 0 ∨ b ≠ 0) → a.natAbs ≤ X → b.natAbs ≤ Y →
      R / 10 < ((|g₁ * a + g₂ * b| : ℤ) : ℝ)) ∨
    ∃ x y : ℤ, (x ≠ 0 ∨ y ≠ 0) ∧ x.natAbs ≤ X ∧ y.natAbs ≤ Y ∧
      (∃ u v : ℤ, u * x + v * y = 1) ∧
      0 < |g₁ * x + g₂ * y| ∧ ((|g₁ * x + g₂ * y| : ℤ) : ℝ) ≤ R / 10 ∧
      1 ≤ chainCapacity x y (X + 1) (Y + 1) ∧
      (∀ s t : ℤ, (s ≠ 0 ∨ t ≠ 0) → s.natAbs ≤ X → t.natAbs ≤ Y →
        |g₁ * x + g₂ * y| ≤ |g₁ * s + g₂ * t|) ∧
      ∀ a b a' b' : ℤ, |a - a'| ≤ (X : ℤ) → |b - b'| ≤ (Y : ℤ) →
        x * b - y * a ≠ x * b' - y * a' →
        (7 / 40 : ℝ) * R * ((chainCapacity x y (X + 1) (Y + 1) : ℝ) + 1) ≤
          ((|(g₁ * a + g₂ * b) - (g₁ * a' + g₂ * b')| : ℤ) : ℝ) := by
  by_cases hs : ∃ a b : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ a.natAbs ≤ X ∧ b.natAbs ≤ Y ∧
      ((|g₁ * a + g₂ * b| : ℤ) : ℝ) ≤ R / 10
  · obtain ⟨a, b, hab, ha, hb, hs⟩ := hs
    obtain ⟨x, y, hxy, hx, hy, hbez, hD, hDhi, hspacing⟩ :=
      rankTwo_short_primitive_spacing hR hspan hproper hab ha hb hs
    have hcap : 1 ≤ chainCapacity x y (X + 1) (Y + 1) :=
      (le_chainCapacity_iff (Nat.succ_pos X) (Nat.succ_pos Y) hxy).2
        (by simp only [Nat.one_mul]; omega)
    exact Or.inr ⟨x, y, hxy, hx, hy, hbez, hD, hDhi, hcap, hspacing,
      fun _ _ _ _ => rankTwo_projected_chain_separation hR.le hX hY hxy hx hy hspan hDhi⟩
  · exact Or.inl (fun a b hab ha hb => lt_of_not_ge (fun hh => hs ⟨a, b, hab, ha, hb, hh⟩))

end Jsp000726
