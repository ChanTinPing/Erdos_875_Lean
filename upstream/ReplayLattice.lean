/-
The discrete-lattice lemmas adapt Mathlib.Algebra.Module.ZLattice.Basic, Apache 2.0.
The determinant argument uses an integral change of basis and uses no measure theory.
-/
module

public import ErdosProblems.Erdos407.PrimitiveExtension
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Data.Int.Order.Units
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section

open Module Submodule Set
open scoped BigOperators

namespace Erdos407.ReplayLattice

private theorem standardSpanDiscrete (n : ℕ) :
    DiscreteTopology (span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))) := by
  refine discreteTopology_iff_isOpen_singleton_zero.mpr ⟨Metric.ball 0 1, Metric.isOpen_ball, ?_⟩
  ext x
  rw [Set.mem_preimage, Metric.mem_ball, dist_zero_right, pi_norm_lt_iff zero_lt_one,
    Set.mem_singleton_iff]
  simp_rw [← Submodule.coe_eq_zero, funext_iff, Pi.zero_apply, Real.norm_eq_abs]
  refine forall_congr' (fun i => ?_)
  suffices h : ∃ y : ℤ, (y : ℝ) = (x : Fin n → ℝ) i by
    obtain ⟨y, hy⟩ := h
    rw [← hy, ← Int.cast_abs, ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff, Int.cast_eq_zero]
  exact ((Pi.basisFun ℝ (Fin n)).mem_span_iff_repr_mem ℤ x).mp (SetLike.coe_mem x) i

theorem finite_span_inter_bounded {n : ℕ} (b : Basis (Fin n) ℝ (Fin n → ℝ))
    {s : Set (Fin n → ℝ)} (hs : Bornology.IsBounded s) :
    Set.Finite (s ∩ span ℤ (Set.range b)) := by
  have h : Set.MapsTo b.equivFun (span ℤ (Set.range b))
      (span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))) := by
    intro _ hx
    rwa [SetLike.mem_coe, Basis.mem_span_iff_repr_mem] at hx ⊢
  let := standardSpanDiscrete n
  have hdiscrete : DiscreteTopology (span ℤ (Set.range b)) := by
    exact DiscreteTopology.of_continuous_injective ((continuous_equivFun_basis b).restrict h)
      (Subtype.map_injective _ (Basis.equivFun b).injective)
  let := hdiscrete
  refine Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete hs ?_
  rw [← coe_toAddSubgroup]
  exact AddSubgroup.isClosed_of_discreteTopology

theorem abs_det_zspan_basis_eq_of_change {n : ℕ}
    (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (B : Basis (Fin n) ℤ (span ℤ (Set.range b))) :
    |(Matrix.of (((↑) : span ℤ (Set.range b) → (Fin n → ℝ)) ∘ B)).det| =
      |(Matrix.of b).det| := by
  classical
  let L := span ℤ (Set.range b)
  let C : Basis (Fin n) ℤ L := Erdos407.PrimitiveExtension.zspanBasis b
  let M := C.toMatrix B
  have hdet_prod : M.det * (B.toMatrix C).det = 1 := by
    dsimp [M]
    rw [← Matrix.det_mul, C.toMatrix_mul_toMatrix_flip B, Matrix.det_one]
  have hunit : IsUnit M.det := isUnit_iff_exists_inv.mpr ⟨_, hdet_prod⟩
  have hcast : |(M.det : ℝ)| = 1 := by
    exact_mod_cast (Int.isUnit_iff_abs_eq.mp hunit)
  have hmatrix : Matrix.of (((↑) : L → (Fin n → ℝ)) ∘ B) =
      (M.map fun x : ℤ ↦ (x : ℝ)).transpose * Matrix.of b := by
    ext i j
    let φ : L →ₗ[ℤ] ℝ := (LinearMap.proj j).comp L.subtype
    have hC (k : Fin n) : ((C k : L) : Fin n → ℝ) = b k :=
      Erdos407.PrimitiveExtension.zspanBasis_apply_coe b k
    have hsum := congrArg φ (C.sum_repr (B i))
    rw [map_sum] at hsum
    simpa only [map_smul, φ, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.proj_apply,
      zsmul_eq_mul, hC, M, Matrix.of_apply, Function.comp_apply, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.map_apply, Basis.toMatrix_apply] using hsum.symm
  change |(Matrix.of (((↑) : L → (Fin n → ℝ)) ∘ B)).det| = _
  rw [hmatrix, Matrix.det_mul, Matrix.det_transpose, ← Int.cast_det, abs_mul, hcast, one_mul]

noncomputable def realBasisFromZSpan {n : ℕ} (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (B : Basis (Fin n) ℤ (span ℤ (Set.range b))) : Basis (Fin n) ℝ (Fin n → ℝ) := by
  let v : Fin n → Fin n → ℝ := fun i => B i
  have hdet : (Matrix.of v).det ≠ 0 := by
    intro hzero
    have heq := abs_det_zspan_basis_eq_of_change b B
    change |(Matrix.of v).det| = |(Matrix.of b).det| at heq
    rw [hzero, abs_zero] at heq
    have hreal : (Pi.basisFun ℝ (Fin n)).det b ≠ 0 :=
      (AlternatingMap.map_basis_ne_zero_iff b (Pi.basisFun ℝ (Fin n)).det).mpr
        (Pi.basisFun ℝ (Fin n)).det_ne_zero
    rw [Pi.basisFun_det_apply] at hreal
    exact hreal (abs_eq_zero.mp heq.symm)
  exact basisOfLinearIndependentOfCardEqFinrank' v
    (Matrix.linearIndependent_rows_of_det_ne_zero hdet)
    (by simp only [Fintype.card_fin, Module.finrank_fin_fun])

@[simp] theorem realBasisFromZSpan_apply {n : ℕ} (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (B : Basis (Fin n) ℤ (span ℤ (Set.range b))) (i : Fin n) :
    realBasisFromZSpan b B i = B i := by
  simp only [realBasisFromZSpan, coe_basisOfLinearIndependentOfCardEqFinrank']

theorem realBasisFromZSpan_span {n : ℕ} (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (B : Basis (Fin n) ℤ (span ℤ (Set.range b))) :
    span ℤ (Set.range (realBasisFromZSpan b B)) = span ℤ (Set.range b) := by
  let L := span ℤ (Set.range b)
  have hrange : Set.range (realBasisFromZSpan b B) = L.subtype '' Set.range B := by
    rw [← Set.range_comp]
    congr 1
    funext i
    exact realBasisFromZSpan_apply b B i
  rw [hrange, ← Submodule.map_span, B.span_eq, Submodule.map_top, Submodule.range_subtype]

end Erdos407.ReplayLattice
