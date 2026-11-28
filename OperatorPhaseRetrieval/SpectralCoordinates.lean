module

public import OperatorPhaseRetrieval.UnitaryLogarithm
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential

@[expose] public section

noncomputable section

-- With all of Mathlib imported, some instance searches in this file need a larger budget.
set_option synthInstance.maxHeartbeats 200000

open NormedSpace
open scoped Matrix Matrix.Norms.L2Operator

namespace OperatorPhaseRetrieval

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A diagonal operator expressed in an arbitrary orthonormal basis. -/
def basisDiagonal (b : OrthonormalBasis ι ℂ E) (v : ι → ℂ) : E →L[ℂ] E :=
  b.repr.symm.conjStarAlgEquiv (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (Matrix.diagonal v))

theorem basisDiagonal_repr (b : OrthonormalBasis ι ℂ E) (v : ι → ℂ) (x : E) (i : ι) :
    b.repr (basisDiagonal b v x) i = v i * b.repr x i := by
  change b.repr (b.repr.symm (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (Matrix.diagonal v) (b.repr x))) i = _
  rw [b.repr.apply_symm_apply]
  change (Matrix.diagonal v *ᵥ (b.repr x).ofLp) i = _
  simp [Matrix.mulVec_diagonal]

theorem basisDiagonal_apply_basis (b : OrthonormalBasis ι ℂ E) (v : ι → ℂ) (j : ι) :
    basisDiagonal b v (b j) = v j • b j := by
  apply b.repr.injective
  ext i
  rw [basisDiagonal_repr]
  simp only [map_smul, PiLp.smul_apply, smul_eq_mul, b.repr_self]
  by_cases hij : i = j
  · subst i; rfl
  · simp [hij]

theorem basisDiagonal_eq_of_apply_basis (b : OrthonormalBasis ι ℂ E) (v : ι → ℂ)
    (A : E →L[ℂ] E) (hA : ∀ j, A (b j) = v j • b j) : basisDiagonal b v = A := by
  apply ContinuousLinearMap.coe_injective
  apply b.toBasis.ext
  intro j
  exact (basisDiagonal_apply_basis b v j).trans (hA j).symm

theorem basisDiagonal_toMatrix (b : OrthonormalBasis ι ℂ E) (v : ι → ℂ) :
    LinearMap.toMatrix b.toBasis b.toBasis (basisDiagonal b v).toLinearMap = Matrix.diagonal v := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  change b.toBasis.repr (basisDiagonal b v (b j)) i = _
  rw [b.coe_toBasis_repr_apply, basisDiagonal_repr]
  simp [Matrix.diagonal_apply, b.repr_self]

theorem basisDiagonal_trace (b : OrthonormalBasis ι ℂ E) (v : ι → ℂ) :
    LinearMap.trace ℂ E (basisDiagonal b v).toLinearMap = ∑ i, v i := by
  rw [LinearMap.trace_eq_matrix_trace ℂ b.toBasis, basisDiagonal_toMatrix, Matrix.trace_diagonal]

theorem basisDiagonal_norm_le (b : OrthonormalBasis ι ℂ E) (v : ι → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hv : ∀ i, ‖v i‖ ≤ C) : ‖basisDiagonal b v‖ ≤ C := by
  rw [basisDiagonal, StarAlgEquiv.norm_map, Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hC).mpr hv

theorem basisDiagonal_smul (b : OrthonormalBasis ι ℂ E) (v : ι → ℂ) (c : ℂ) :
    basisDiagonal b (fun i => c * v i) = c • basisDiagonal b v := by
  apply basisDiagonal_eq_of_apply_basis
  intro j
  simp [basisDiagonal_apply_basis, smul_smul]

theorem basisDiagonal_isSelfAdjoint (b : OrthonormalBasis ι ℂ E) (v : ι → ℝ) :
    IsSelfAdjoint (basisDiagonal b (fun i => (v i : ℂ))) := by
  unfold basisDiagonal
  apply IsSelfAdjoint.map
  apply IsSelfAdjoint.map
  rw [isSelfAdjoint_iff]
  ext i j
  by_cases hij : i = j
  · subst j; simp [Matrix.star_apply]
  · simp [Matrix.star_apply, hij, Ne.symm hij]

theorem basisDiagonal_exp (b : OrthonormalBasis ι ℂ E) (v : ι → ℂ) :
    NormedSpace.exp (basisDiagonal b v) = basisDiagonal b (fun i => Complex.exp (v i)) := by
  unfold basisDiagonal
  rw [← NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) b.repr.symm.conjStarAlgEquiv
      (StarAlgEquiv.isometry b.repr.symm.conjStarAlgEquiv).continuous _ (by simp [expSeries_radius_eq_top]),
    ← NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ))
      (StarAlgEquiv.isometry _).continuous _ (by simp [expSeries_radius_eq_top]), Matrix.exp_diagonal]
  simp only [Pi.exp_def, Complex.exp_eq_exp_ℂ]

end OperatorPhaseRetrieval

end
