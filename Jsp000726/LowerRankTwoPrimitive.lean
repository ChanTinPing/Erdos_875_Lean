module

public import Mathlib.Data.Int.GCD
public import Mathlib.Algebra.Order.Ring.Abs

import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726

/-- A nonzero integer direction is a positive integer multiple of a direction
with a Bézout identity. Each coordinate and each integer linear image weakly
decreases in absolute value under this normalization. -/
theorem exists_primitive_int_direction {a b : ℤ} (h : a ≠ 0 ∨ b ≠ 0) (g₁ g₂ : ℤ) :
    ∃ (k : ℕ) (x y : ℤ), 0 < k ∧ a = (k : ℤ) * x ∧ b = (k : ℤ) * y ∧
      (∃ u v : ℤ, u * x + v * y = 1) ∧
      |x| ≤ |a| ∧ |y| ≤ |b| ∧ |g₁ * x + g₂ * y| ≤ |g₁ * a + g₂ * b| := by
  let k := Int.gcd a b
  obtain ⟨x, hx⟩ := Int.gcd_dvd_left a b
  obtain ⟨y, hy⟩ := Int.gcd_dvd_right a b
  change a = (k : ℤ) * x at hx
  change b = (k : ℤ) * y at hy
  have hk : 0 < k := by
    by_contra! hh
    have hkz : k = 0 := Nat.eq_zero_of_le_zero hh
    exact h.elim (fun ha => ha (by simp [hx, hkz])) (fun hb => hb (by simp [hy, hkz]))
  have hk₁ : (1 : ℤ) ≤ k := Int.ofNat_le.mpr hk
  have hkne : (k : ℤ) ≠ 0 := ne_of_gt (zero_lt_one.trans_le hk₁)
  have haux (w z : ℤ) (hzw : z = (k : ℤ) * w) : |w| ≤ |z| := by
    rw [hzw, abs_mul, abs_of_nonneg (Int.natCast_nonneg k)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hk₁ (abs_nonneg w)
  refine ⟨k, x, y, hk, hx, hy, ?_, haux _ _ hx, haux _ _ hy, ?_⟩
  · let u := a.gcdA b
    let v := a.gcdB b
    refine ⟨u, v, ?_⟩
    apply mul_left_cancel₀ hkne
    calc
      (k : ℤ) * (u * x + v * y) = ((k : ℤ) * x) * u + ((k : ℤ) * y) * v := by ring
      _ = a * u + b * v := by rw [← hx, ← hy]
      _ = (k : ℤ) * 1 := by rw [mul_one]; exact (Int.gcd_eq_gcd_ab a b).symm
  · apply haux
    rw [hx, hy]
    ring

/-- Every integer vector collinear with a Bézout-normalized vector is an integer
multiple of it. -/
theorem int_collinear_multiple {x y a b : ℤ}
    (hbase : ∃ u v : ℤ, u * x + v * y = 1) (hdet : x * b = y * a) :
    ∃ m : ℤ, a = m * x ∧ b = m * y := by
  obtain ⟨u, v, hb⟩ := hbase
  refine ⟨u * a + v * b, ?_, ?_⟩
  · calc
      a = (u * x + v * y) * a := by rw [hb, one_mul]
      _ = (u * a) * x + v * (y * a) := by ring
      _ = _ := by rw [← hdet]; ring
  · calc
      b = (u * x + v * y) * b := by rw [hb, one_mul]
      _ = (v * b) * y + u * (x * b) := by ring
      _ = _ := by rw [hdet]; ring

/-- Equality of the transverse integer labels characterizes two points in the
same parallel chain. -/
theorem int_chain_same_label_iff {x y a b c d : ℤ}
    (hbase : ∃ u v : ℤ, u * x + v * y = 1) :
    x * b - y * a = x * d - y * c ↔
      ∃ m : ℤ, a = c + m * x ∧ b = d + m * y := by
  constructor
  · intro h
    have hd : x * (b - d) = y * (a - c) := by
      rw [mul_sub, mul_sub]
      omega
    obtain ⟨m, ha, hb⟩ := int_collinear_multiple hbase hd
    exact ⟨m, by omega, by omega⟩
  · rintro ⟨m, rfl, rfl⟩
    ring

end Jsp000726
