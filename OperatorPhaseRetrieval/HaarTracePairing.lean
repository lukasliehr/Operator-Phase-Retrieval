module

public import OperatorPhaseRetrieval.HaarBasisChange

@[expose] public section

noncomputable section

open MeasureTheory NormedSpace
open scoped InnerProductSpace

namespace OperatorPhaseRetrieval

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℂ E] in
theorem operator_trace_eq_sum_inner (b : OrthonormalBasis ι ℂ E) (A : E →L[ℂ] E) :
    LinearMap.trace ℂ E A.toLinearMap = ∑ i, inner ℂ (b i) (A (b i)) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ b.toBasis]
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro i _
  change LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap i i = _
  rw [LinearMap.toMatrix_apply, b.coe_toBasis_repr_apply, b.repr_apply_apply]
  simp only [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe]

theorem basisDiagonal_quadratic (b : OrthonormalBasis ι ℂ E) (a : ι → ℝ) (x : E) :
    inner ℂ x (basisDiagonal b (fun i => (a i : ℂ)) x) =
      ∑ i, (a i : ℂ) * (‖b.repr x i‖ ^ 2 : ℝ) := by
  rw [← b.repr.inner_map_map, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [basisDiagonal_repr]
  change inner ℂ (b.repr x i) ((a i : ℂ) • b.repr x i) = _
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
  rfl

theorem unitary_conjugate_quadratic (U : HaarUnitary E) (A : E →L[ℂ] E) (x : E) :
    inner ℂ x (((U : E →L[ℂ] E) * A * (U⁻¹ : HaarUnitary E)) x) =
      inner ℂ (((U⁻¹ : HaarUnitary E) : E →L[ℂ] E) x) (A (((U⁻¹ : HaarUnitary E) : E →L[ℂ] E) x)) := by
  let e := Unitary.linearIsometryEquiv U
  have h := e.inner_map_map (e.symm x) (A (e.symm x))
  rw [e.apply_symm_apply] at h
  exact h

omit [DecidableEq ι] in
theorem unitary_inverse_coordinate_norm (b c : OrthonormalBasis ι ℂ E)
    (U : HaarUnitary E) (i j : ι) :
    ‖c.repr (((U⁻¹ : HaarUnitary E) : E →L[ℂ] E) (b i)) j‖ =
      ‖inner ℂ (b i) ((U : E →L[ℂ] E) (c j))‖ := by
  let e := Unitary.linearIsometryEquiv U
  have h := e.inner_map_map (c j) (e.symm (b i))
  rw [e.apply_symm_apply] at h
  rw [c.repr_apply_apply]
  change ‖inner ℂ (c j) (e.symm (b i))‖ = ‖inner ℂ (b i) (e (c j))‖
  rw [← h, norm_inner_symm]

theorem trace_diagonal_mul (b : OrthonormalBasis ι ℂ E) (β : ι → ℝ) (A : E →L[ℂ] E) :
    LinearMap.trace ℂ E ((basisDiagonal b (fun i => (β i : ℂ))) * A).toLinearMap =
      ∑ i, (β i : ℂ) * inner ℂ (b i) (A (b i)) := by
  rw [operator_trace_eq_sum_inner b]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℂ (b i) (basisDiagonal b (fun i => (β i : ℂ)) (A (b i))) = _
  rw [← b.repr_apply_apply, basisDiagonal_repr, b.repr_apply_apply]

/-- The trace of a Hermitian test operator against a conjugate is the proved
Haar coordinate pairing in the two eigenbases. -/
theorem trace_conjugate_diagonals (b c : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι))
    (a β : ι → ℝ) (U : HaarUnitary (EuclideanSpace ℂ ι)) :
    (LinearMap.trace ℂ (EuclideanSpace ℂ ι)
      ((basisDiagonal b (fun i => (β i : ℂ))) *
        ((U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) *
          basisDiagonal c (fun j => (a j : ℂ)) * ((U⁻¹ : HaarUnitary (EuclideanSpace ℂ ι)) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι))).toLinearMap).re =
      crossHaarPairing ι b c a β U := by
  rw [trace_diagonal_mul]
  simp_rw [unitary_conjugate_quadratic, basisDiagonal_quadratic,
    unitary_inverse_coordinate_norm b c U]
  simp [crossHaarPairing, Finset.mul_sum, mul_assoc, -Complex.ofReal_pow]

theorem basisDiagonal_mul (b : OrthonormalBasis ι ℂ E) (v w : ι → ℂ) :
    basisDiagonal b (fun i => v i * w i) = basisDiagonal b v * basisDiagonal b w := by
  apply basisDiagonal_eq_of_apply_basis
  intro j
  simp [basisDiagonal_apply_basis, smul_smul, mul_comm]

/-- A selfadjoint operator on Euclidean space has real diagonal coefficients in
an orthonormal basis indexed by the same coordinate type. -/
theorem exists_selfAdjoint_diagonal
    (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (hA : IsSelfAdjoint A) :
    ∃ (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (a : ι → ℝ),
      basisDiagonal b (fun i => (a i : ℂ)) = A := by
  have hn : Module.finrank ℂ (EuclideanSpace ℂ ι) = Fintype.card ι := by simp
  let hS : A.toLinearMap.IsSymmetric := hA.isSymmetric
  let b₀ : OrthonormalBasis (Fin (Fintype.card ι)) ℂ (EuclideanSpace ℂ ι) := hS.eigenvectorBasis hn
  let a₀ : Fin (Fintype.card ι) → ℝ := hS.eigenvalues hn
  let e := (Fintype.equivFin ι).symm
  refine ⟨b₀.reindex e, fun i => a₀ (e.symm i), ?_⟩
  apply basisDiagonal_eq_of_apply_basis
  intro j
  simp only [OrthonormalBasis.reindex_apply]
  convert! hS.apply_eigenvectorBasis hn (e.symm j) using 1

/-- Real part of the usual complex linear trace. -/
def operatorRealTrace (A : E →L[ℂ] E) : ℝ := (LinearMap.trace ℂ E A.toLinearMap).re

theorem operatorRealTrace_basisDiagonal (b : OrthonormalBasis ι ℂ E) (a : ι → ℝ) :
    operatorRealTrace (basisDiagonal b (fun i => (a i : ℂ))) = ∑ i, a i := by
  simp [operatorRealTrace, basisDiagonal_trace]

theorem operatorRealTrace_basisDiagonal_sq (b : OrthonormalBasis ι ℂ E) (a : ι → ℝ) :
    operatorRealTrace ((basisDiagonal b (fun i => (a i : ℂ))) ^ 2) = ∑ i, (a i) ^ 2 := by
  rw [pow_two, ← basisDiagonal_mul]
  simp [operatorRealTrace, basisDiagonal_trace, pow_two]

/-- The centered Haar adjoint covariance for arbitrary selfadjoint operators. -/
theorem haar_adjoint_secondMoment [Nonempty ι]
    (A B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (ha : operatorRealTrace A = 0)
    (hn : 1 < Fintype.card ι) :
    (∫ U : HaarUnitary (EuclideanSpace ℂ ι),
      (operatorRealTrace (B * ((U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) * A *
        ((U⁻¹ : HaarUnitary (EuclideanSpace ℂ ι)) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)))) ^ 2
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) =
    operatorRealTrace (A ^ 2) / ((Fintype.card ι : ℝ) ^ 2 - 1) *
      (operatorRealTrace (B ^ 2) - (operatorRealTrace B) ^ 2 / Fintype.card ι) := by
  obtain ⟨c, a, rfl⟩ := exists_selfAdjoint_diagonal A hA
  obtain ⟨b, β, rfl⟩ := exists_selfAdjoint_diagonal B hB
  rw [operatorRealTrace_basisDiagonal] at ha
  simp only [operatorRealTrace_basisDiagonal_sq, operatorRealTrace_basisDiagonal]
  change (∫ U : HaarUnitary (EuclideanSpace ℂ ι),
    ((LinearMap.trace ℂ (EuclideanSpace ℂ ι)
      ((basisDiagonal b (fun i => (β i : ℂ))) *
        ((U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) *
          basisDiagonal c (fun j => (a j : ℂ)) * ((U⁻¹ : HaarUnitary (EuclideanSpace ℂ ι)) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι))).toLinearMap).re) ^ 2
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) = _
  simp_rw [trace_conjugate_diagonals, pow_two]
  simpa only [pow_two] using crossHaarPairing_covariance ι b c a a β β ha hn

end OperatorPhaseRetrieval

end
