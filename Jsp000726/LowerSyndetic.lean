module

public import Jsp000726.LowerDiscrete
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

namespace Jsp000726

open Finset

/-- Two sampled syndetic sets whose cardinality functions agree on cross-sum relations
force any sublinear first cardinality function to be bounded. -/
theorem bounded_of_cross_sum_compatible (F G : ℕ → ℤ) (x y : ℕ → ℕ) {P Q : ℕ}
    (hx : ∀ n, n ≤ x n ∧ x n ≤ n + P) (hy : ∀ n, n ≤ y n ∧ y n ≤ n + Q)
    (hcompat : ∀ i j i' j', x i + y j = x i' + y j' → F i + G j = F i' + G j')
    (hF0 : F 0 = 0)
    (hslow : ∀ K : ℕ, ∃ C : ℕ, ∀ n : ℕ, (K : ℤ) * F n ≤ (n : ℤ) + C) :
    ∃ B : ℤ, ∀ n, F n ≤ B := by
  classical
  let diff (i j : ℕ) : ℤ := (y j : ℤ) - x i
  let k (d : ℤ) : ℤ := if h : ∃ p : ℕ × ℕ, diff p.1 p.2 = d then
    G h.choose.2 - F h.choose.1 else 0
  have hk (i j : ℕ) : k (diff i j) = G j - F i := by
    have h : ∃ p : ℕ × ℕ, diff p.1 p.2 = diff i j := ⟨(i, j), rfl⟩
    have hd := h.choose_spec
    have heq : x h.choose.1 + y j = x i + y h.choose.2 := by
      dsimp only [diff] at hd
      omega
    have hf := hcompat _ _ _ _ heq
    simp only [k, dite_eq_left h]
    omega
  let near := (range (P + Q + 3)).image fun i : ℕ => k ((i : ℤ) - P - 1)
  let M := near.sup Int.natAbs
  have hknear {d : ℤ} (hlo : -(P : ℤ) - 1 ≤ d) (hhi : d ≤ (Q : ℤ) + 1) :
      |k d| ≤ (M : ℤ) := by
    let i := (d + (P : ℤ) + 1).toNat
    have hiEq : (i : ℤ) = d + P + 1 := Int.toNat_of_nonneg (by omega)
    have hinear : i ∈ range (P + Q + 3) := by apply mem_range.mpr; omega
    have hing : k d ∈ near := by
      apply mem_image.mpr
      exact ⟨i, hinear, congrArg k (by omega)⟩
    have hsup : (k d).natAbs ≤ M := Finset.le_sup (f := Int.natAbs) hing
    exact Int.natCast_natAbs (k d) ▸ Int.ofNat_le.mpr hsup
  have hfn (n : ℕ) : |F (n + 1) - F n| ≤ ((2 * M : ℕ) : ℤ) := by
    have h₁ := hx n
    have h₂ := hx (n + 1)
    have h₃ := hy n
    have hA := hknear (d := diff n n) (by dsimp [diff]; omega) (by dsimp [diff]; omega)
    have hB := hknear (d := diff (n + 1) n) (by dsimp [diff]; omega) (by dsimp [diff]; omega)
    rw [hk] at hA hB
    have hA' := abs_le.mp hA
    have hB' := abs_le.mp hB
    exact abs_le.mpr ⟨by omega, by omega⟩
  have hgn (n : ℕ) : |G (n + 1) - G n| ≤ ((2 * M : ℕ) : ℤ) := by
    have h₁ := hx n
    have h₂ := hy n
    have h₃ := hy (n + 1)
    have hA := hknear (d := diff n n) (by dsimp [diff]; omega) (by dsimp [diff]; omega)
    have hB := hknear (d := diff n (n + 1)) (by dsimp [diff]; omega) (by dsimp [diff]; omega)
    rw [hk] at hA hB
    have hA' := abs_le.mp hA
    have hB' := abs_le.mp hB
    exact abs_le.mpr ⟨by omega, by omega⟩
  let H (d n : ℕ) := G (n + d) - F n
  let vals (d : ℕ) := (range (P + Q + 1)).image fun i : ℕ => k ((d : ℤ) - P + i)
  have hvals (d n : ℕ) : H d n ∈ vals d := by
    have h₁ := hx n
    have h₂ := hy (n + d)
    let i := (diff n (n + d) - (d : ℤ) + P).toNat
    have hiEq : (i : ℤ) = diff n (n + d) - d + P :=
      Int.toNat_of_nonneg (by dsimp [diff]; omega)
    have himem : i ∈ range (P + Q + 1) := by
      apply mem_range.mpr
      dsimp only [diff] at hiEq
      omega
    apply mem_image.mpr
    refine ⟨i, himem, ?_⟩
    rw [show (d : ℤ) - P + i = diff n (n + d) by omega, hk]
  have hHstep (d n : ℕ) : |H d (n + 1) - H d n| ≤ ((4 * M : ℕ) : ℤ) := by
    have hF := abs_le.mp (hfn n)
    have hG := abs_le.mp (hgn (n + d))
    have hn : n + 1 + d = n + d + 1 := by omega
    dsimp only [H]
    rw [hn]
    exact abs_le.mpr ⟨by omega, by omega⟩
  let T : ℤ := (((4 * M : ℕ) : ℤ) + 1) * ((P + Q + 1 : ℕ) : ℤ)
  have hosc (d t b : ℕ) : |H d (b + t) - H d b| ≤ T := by
    have hstep' (j : ℕ) : |H d (b + (j + 1)) - H d (b + j)| ≤ ((4 * M : ℕ) : ℤ) := by
      rw [← Nat.add_assoc]
      exact hHstep d (b + j)
    have hb := integer_walk_abs_le (f := fun j => H d (b + j)) (s := vals d)
      (fun j => hvals d (b + j)) hstep' t
    rw [Nat.add_zero] at hb
    have hcard : (vals d).card ≤ P + Q + 1 := by
      calc
        _ ≤ (range (P + Q + 1)).card := card_image_le
        _ = _ := card_range _
    exact hb.trans (mul_le_mul_of_nonneg_left (Int.ofNat_le.mpr hcard) (by omega))
  have hdefect (t d : ℕ) : F t + F d - 2 * T ≤ F (t + d) := by
    have h₁ := (abs_le.mp (hosc d t 0)).1
    have h₂ := (abs_le.mp (hosc 0 t d)).2
    have heq : d + t = t + d := Nat.add_comm _ _
    dsimp only [H] at h₁ h₂
    simp only [Nat.zero_add, hF0, sub_zero] at h₁
    simp only [Nat.add_zero, heq] at h₂
    omega
  refine ⟨2 * T, fun d => ?_⟩
  by_contra! hd
  have hind (m : ℕ) : (m : ℤ) ≤ F (m * d) := by
    induction m with
    | zero => simp [hF0]
    | succ m ih =>
        rw [Nat.succ_mul]
        have h := hdefect (m * d) d
        omega
  obtain ⟨C, hC⟩ := hslow (d + 1)
  let m := C + 1
  have hlarge := hind m
  have hbound := hC (m * d)
  have hprod := mul_le_mul_of_nonneg_left hlarge
    (show (0 : ℤ) ≤ ((d + 1 : ℕ) : ℤ) by omega)
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hbound
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, mul_comm (d : ℤ) (m : ℤ)] at hprod
  omega

end Jsp000726
