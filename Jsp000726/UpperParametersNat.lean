module

public import Jsp000726.UpperParameters

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace Jsp000726.Upper

/-- Next period, chosen as the first multiple of `d` strictly above `16 r`. -/
def sharpK (r d : ℕ) : ℕ := d * (16 * r / d + 1)

/-- The number of terms in the dense block. -/
def sharpBlock (C r : ℕ) : ℕ := C * r ^ 2

/-- Row of the next reference. -/
def sharpQ (k K : ℕ) : ℕ := 64 * k ^ 2 / K + 1

/-- The remaining row height after reserving the cubic filler and dense block. -/
def sharpH (N r k R : ℕ) : ℕ := R - k - r ^ 3 / N ^ 3

theorem sharpK_dvd (r d : ℕ) : d ∣ sharpK r d := dvd_mul_right d _

theorem sharpK_bounds {r d : ℕ} (hd : 0 < d) (hdr : d ≤ r) :
    16 * r < sharpK r d ∧ sharpK r d ≤ 17 * r := by
  constructor
  · exact Nat.lt_mul_div_succ (16 * r) hd
  · unfold sharpK
    rw [Nat.mul_add, Nat.mul_one]
    have hm := Nat.mul_div_le (16 * r) d
    omega

private theorem sharpBlock_ge_factor {C r : ℕ} (hr : 0 < r) :
    C * r ≤ sharpBlock C r := by
  unfold sharpBlock
  apply Nat.mul_le_mul_left
  calc
    r = r * 1 := (Nat.mul_one r).symm
    _ ≤ r * r := Nat.mul_le_mul_left r hr
    _ = r ^ 2 := (pow_two r).symm

theorem two_mul_sharpK_le_block {C r d : ℕ} (hC : 100 ≤ C) (hd : 0 < d) (hdr : d ≤ r) :
    2 * sharpK r d ≤ sharpBlock C r := by
  calc
    2 * sharpK r d ≤ 2 * (17 * r) := Nat.mul_le_mul_left 2 (sharpK_bounds hd hdr).2
    _ = 34 * r := by ring
    _ ≤ C * r := Nat.mul_le_mul_right r (by omega)
    _ ≤ sharpBlock C r := sharpBlock_ge_factor (hd.trans_le hdr)

theorem add_le_sharpBlock {N C r : ℕ} (hr : 0 < r) (hNr : N ≤ r) (hC : 100 ≤ C) :
    N + r ≤ sharpBlock C r := by
  calc
    N + r ≤ 2 * r := by omega
    _ ≤ C * r := Nat.mul_le_mul_right r (by omega)
    _ ≤ sharpBlock C r := sharpBlock_ge_factor hr

theorem sharpQ_mul_bounds {k K : ℕ} (hK : 0 < K) :
    64 * k ^ 2 < K * sharpQ k K ∧ K * sharpQ k K ≤ 64 * k ^ 2 + K := by
  constructor
  · exact Nat.lt_mul_div_succ (64 * k ^ 2) hK
  · unfold sharpQ
    rw [Nat.mul_add, Nat.mul_one]
    exact Nat.add_le_add_right (Nat.mul_div_le (64 * k ^ 2) K) K

theorem two_mul_lt_sharpQ {k K : ℕ} (hK : 0 < K) (hKk : K ≤ k) :
    2 * k < sharpQ k K := by
  have hk : 0 < k := hK.trans_le hKk
  apply Nat.lt_of_mul_lt_mul_left (a := K)
  calc
    K * (2 * k) ≤ k * (2 * k) := Nat.mul_le_mul_right _ hKk
    _ = 2 * k ^ 2 := by ring
    _ ≤ 64 * k ^ 2 := by omega
    _ < K * sharpQ k K := (sharpQ_mul_bounds hK).1

theorem sharpH_pos_and_end {N r k K : ℕ}
    (hN : 0 < N) (hNr : r ≤ N ^ 2) (hK : 0 < K) (hKk : K ≤ k) (hrk : r ^ 2 ≤ k) :
    0 < sharpH N r k (sharpQ k K) ∧
      r ^ 3 / N ^ 3 + sharpH N r k (sharpQ k K) = sharpQ k K - k := by
  have hdiv : r ^ 3 / N ^ 3 ≤ r ^ 2 := by
    apply Nat.div_le_of_le_mul
    calc
      r ^ 3 = r ^ 2 * r := by ring
      _ ≤ r ^ 2 * N ^ 2 := Nat.mul_le_mul_left _ hNr
      _ ≤ r ^ 2 * N ^ 3 := Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right hN (by decide))
      _ = N ^ 3 * r ^ 2 := Nat.mul_comm _ _
  have hR := two_mul_lt_sharpQ hK hKk
  unfold sharpH
  omega

theorem sharpReference_bounds {B k K : ℕ} (hK : 0 < K) (hKk : 2 * K ≤ k) :
    64 * B * k ^ 2 ≤ B + B * K * sharpQ k K ∧
      B + B * K * sharpQ k K ≤ 65 * B * k ^ 2 := by
  have hk : 2 ≤ k := by omega
  have hksq : 2 * k ≤ k ^ 2 := by
    simpa [pow_two, Nat.mul_comm] using Nat.mul_le_mul_left k hk
  have hkK : 1 + K ≤ k ^ 2 := by omega
  have hQ := sharpQ_mul_bounds (k := k) hK
  constructor
  · calc
      64 * B * k ^ 2 = B * (64 * k ^ 2) := by ring
      _ ≤ B * (K * sharpQ k K) := Nat.mul_le_mul_left _ hQ.1.le
      _ ≤ B + B * K * sharpQ k K := by rw [mul_assoc]; omega
  · calc
      B + B * K * sharpQ k K = B * (1 + K * sharpQ k K) := by ring
      _ ≤ B * (65 * k ^ 2) := Nat.mul_le_mul_left _ (by omega)
      _ = 65 * B * k ^ 2 := by ring

end Jsp000726.Upper
