module

public import Jsp000726.LowerRankTwoPrimitive
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Finset.Max

import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726

/-- The number of whole steps of a nonzero direction that fit in a box. -/
def chainCapacity (x y : ℤ) (L₁ L₂ : ℕ) : ℕ :=
  if x = 0 then (L₂ - 1) / y.natAbs
  else if y = 0 then (L₁ - 1) / x.natAbs
  else min ((L₁ - 1) / x.natAbs) ((L₂ - 1) / y.natAbs)

theorem le_chainCapacity_iff {x y : ℤ} {L₁ L₂ t : ℕ} (h₁ : 0 < L₁) (h₂ : 0 < L₂)
    (hxy : x ≠ 0 ∨ y ≠ 0) :
    t ≤ chainCapacity x y L₁ L₂ ↔ t * x.natAbs < L₁ ∧ t * y.natAbs < L₂ := by
  have branch {d : ℤ} {L : ℕ} (hd : d ≠ 0) (hL : 0 < L) :
      t ≤ (L - 1) / d.natAbs ↔ t * d.natAbs < L := by
    rw [Nat.le_div_iff_mul_le (Int.natAbs_pos.mpr hd)]
    omega
  by_cases hx : x = 0
  · have hy : y ≠ 0 := hxy.resolve_left (fun hnx => hnx hx)
    simp [chainCapacity, hx, h₁, branch hy h₂]
  · by_cases hy : y = 0
    · simp [chainCapacity, hx, hy, h₂, branch hx h₁]
    · simp only [chainCapacity, ite_eq_right hx, ite_eq_right hy, le_min_iff, branch hx h₁, branch hy h₂]

/-- Coordinate of a directed chain, starting from the appropriate face. -/
def chainCoord (d : ℤ) (q j : ℕ) : ℤ :=
  if 0 ≤ d then (j : ℤ) * d else ((j : ℤ) - q) * d

theorem chainCoord_step (d : ℤ) (q j : ℕ) :
    chainCoord d q j = chainCoord d q 0 + (j : ℤ) * d := by
  by_cases hd : 0 ≤ d <;> simp only [chainCoord, hd, ite_true, ite_false, Nat.cast_zero] <;> ring

private theorem chainCoord_bounds {d : ℤ} {q j L : ℕ} (hcap : q * d.natAbs < L)
    (hj : j ≤ q) : 0 ≤ chainCoord d q j ∧ chainCoord d q j < (L : ℤ) := by
  have hLj : (q : ℤ) * |d| < (L : ℤ) := by
    rw [← Int.natCast_natAbs, ← Nat.cast_mul]
    exact Int.ofNat_lt.mpr hcap
  have hjq : (j : ℤ) ≤ (q : ℤ) := Int.ofNat_le.mpr hj
  by_cases hd : 0 ≤ d
  · simp only [chainCoord, ite_eq_left hd]
    exact ⟨mul_nonneg (Int.natCast_nonneg _) hd,
      (mul_le_mul_of_nonneg_right hjq hd).trans_lt (by simpa only [abs_of_nonneg hd] using hLj)⟩
  · simp only [chainCoord, ite_eq_right hd]
    have hdn : d ≤ 0 := le_of_not_ge hd
    have heq : ((j : ℤ) - q) * d = ((q : ℤ) - j) * (-d) := by ring
    rw [heq]
    exact ⟨mul_nonneg (sub_nonneg.mpr hjq) (neg_nonneg.mpr hdn),
      (mul_le_mul_of_nonneg_right (by omega : (q : ℤ) - j ≤ q) (neg_nonneg.mpr hdn)).trans_lt
        (by simpa only [abs_of_nonpos hdn] using hLj)⟩

/-- A chain of the full capacity is realized inside the box and its projection
is an arithmetic progression with the direction's projected integer step. -/
theorem full_box_chain {x y : ℤ} {L₁ L₂ : ℕ} (h₁ : 0 < L₁) (h₂ : 0 < L₂)
    (hxy : x ≠ 0 ∨ y ≠ 0) (g₁ g₂ : ℤ) :
    let q := chainCapacity x y L₁ L₂
    ∃ b : ℤ, ∀ j : ℕ, j ≤ q →
      ∃ a₁ a₂ : ℤ, 0 ≤ a₁ ∧ a₁ < L₁ ∧ 0 ≤ a₂ ∧ a₂ < L₂ ∧
        g₁ * a₁ + g₂ * a₂ = b + (j : ℤ) * (g₁ * x + g₂ * y) := by
  intro q
  have hcap := (le_chainCapacity_iff h₁ h₂ hxy).1 (show q ≤ chainCapacity x y L₁ L₂ from le_rfl)
  refine ⟨g₁ * chainCoord x q 0 + g₂ * chainCoord y q 0, fun j hj => ?_⟩
  have ha := chainCoord_bounds hcap.1 hj
  have hb := chainCoord_bounds hcap.2 hj
  refine ⟨chainCoord x q j, chainCoord y q j, ha.1, ha.2, hb.1, hb.2, ?_⟩
  rw [chainCoord_step x q j, chainCoord_step y q j]
  ring

/-- The full chain may be oriented to have a nonnegative projection step. -/
theorem full_box_chain_abs {x y : ℤ} {L₁ L₂ : ℕ} (h₁ : 0 < L₁) (h₂ : 0 < L₂)
    (hxy : x ≠ 0 ∨ y ≠ 0) (g₁ g₂ : ℤ) :
    let q := chainCapacity x y L₁ L₂
    ∃ b : ℤ, ∀ j : ℕ, j ≤ q →
      ∃ a₁ a₂ : ℤ, 0 ≤ a₁ ∧ a₁ < L₁ ∧ 0 ≤ a₂ ∧ a₂ < L₂ ∧
        g₁ * a₁ + g₂ * a₂ = b + (j : ℤ) * |g₁ * x + g₂ * y| := by
  intro q
  obtain ⟨b, hb⟩ := full_box_chain h₁ h₂ hxy g₁ g₂
  let g := g₁ * x + g₂ * y
  change ∃ b : ℤ, ∀ j : ℕ, j ≤ q →
    ∃ a₁ a₂ : ℤ, 0 ≤ a₁ ∧ a₁ < L₁ ∧ 0 ≤ a₂ ∧ a₂ < L₂ ∧
        g₁ * a₁ + g₂ * a₂ = b + (j : ℤ) * |g|
  by_cases hg : 0 ≤ g
  · exact ⟨b, fun j hj => by simpa only [abs_of_nonneg hg] using hb j hj⟩
  · refine ⟨b + (q : ℤ) * g, fun j hj => ?_⟩
    obtain ⟨a₁, a₂, ha₁, ha₂, ha₃, ha₄, ha⟩ := hb (q - j) (Nat.sub_le _ _)
    change g₁ * a₁ + g₂ * a₂ = b + ((q - j : ℕ) : ℤ) * g at ha
    refine ⟨a₁, a₂, ha₁, ha₂, ha₃, ha₄, ?_⟩
    rw [ha, Nat.cast_sub hj, abs_of_nonpos (le_of_not_ge hg)]
    ring

/-- A fixed transverse label contains no more points in the box than the
length of a full chain. -/
theorem card_box_chain_le {x y : ℤ} {L₁ L₂ : ℕ}
    (h₁ : 0 < L₁) (h₂ : 0 < L₂) (hxy : x ≠ 0 ∨ y ≠ 0)
    (hbase : ∃ u v : ℤ, u * x + v * y = 1) (S : Finset (ℤ × ℤ)) (k : ℤ)
    (box : ∀ p ∈ S, 0 ≤ p.1 ∧ p.1 < L₁ ∧ 0 ≤ p.2 ∧ p.2 < L₂)
    (label : ∀ p ∈ S, x * p.2 - y * p.1 = k) :
    S.card ≤ chainCapacity x y L₁ L₂ + 1 := by
  classical
  obtain ⟨u, v, hb⟩ := hbase
  let f (p : ℤ × ℤ) := u * p.1 + v * p.2
  let q := chainCapacity x y L₁ L₂
  have hpair {p p' : ℤ × ℤ} (hp : p ∈ S) (hp' : p' ∈ S) :
      ∃ m : ℤ, p.1 = p'.1 + m * x ∧ p.2 = p'.2 + m * y ∧ f p - f p' = m ∧ m.natAbs ≤ q := by
    have hl := (label p hp).trans (label p' hp').symm
    obtain ⟨m, hh₁, hh₂⟩ := (int_chain_same_label_iff ⟨u, v, hb⟩).1 hl
    have hf : f p - f p' = m := by
      change u * p.1 + v * p.2 - (u * p'.1 + v * p'.2) = m
      rw [hh₁, hh₂]
      calc
        _ = m * (u * x + v * y) := by ring
        _ = m := by rw [hb, mul_one]
    have hLx : |m * x| < (L₁ : ℤ) := by
      have heq : m * x = p.1 - p'.1 := by omega
      rw [heq, abs_lt]
      have h := box p hp
      have h' := box p' hp'
      omega
    have hLy : |m * y| < (L₂ : ℤ) := by
      have heq : m * y = p.2 - p'.2 := by omega
      rw [heq, abs_lt]
      have h := box p hp
      have h' := box p' hp'
      omega
    have hm := (le_chainCapacity_iff h₁ h₂ hxy).2 ⟨
      by rw [← Int.natAbs_mul]; exact Int.ofNat_lt.mp (by rwa [Int.natCast_natAbs]),
      by rw [← Int.natAbs_mul]; exact Int.ofNat_lt.mp (by rwa [Int.natCast_natAbs])⟩
    exact ⟨m, hh₁, hh₂, hf, hm⟩
  have hfinj : Set.InjOn f S := by
    intro p hp p' hp' hpp
    obtain ⟨m, hh₁, hh₂, hhf, _⟩ := hpair hp hp'
    have hm : m = 0 := by omega
    exact Prod.ext (by simpa [hm] using hh₁) (by simpa [hm] using hh₂)
  by_cases hne : S.Nonempty
  · let I := S.image f
    have hI : I.Nonempty := Finset.Nonempty.image hne _
    let low := I.min' hI
    have hlow : low ∈ I := Finset.min'_mem I hI
    obtain ⟨p', hp', hplow⟩ := Finset.mem_image.mp hlow
    have hsub : I ⊆ Finset.Icc low (low + q) := by
      intro z hz
      have hmin := Finset.min'_le I z hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨m, _, _, hfp, hmq⟩ := hpair hp hp'
      have hmcast : |m| ≤ (q : ℤ) := by
        rw [← Int.natCast_natAbs]
        exact Int.ofNat_le.mpr hmq
      exact Finset.mem_Icc.mpr ⟨hmin, by
        have hmle := (le_abs_self m).trans hmcast
        omega⟩
    calc
      S.card = I.card := (Finset.card_image_of_injOn hfinj).symm
      _ ≤ (Finset.Icc low (low + q)).card := Finset.card_le_card hsub
      _ = q + 1 := by rw [Int.card_Icc]; omega
  · have hs := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hs]

end Jsp000726
