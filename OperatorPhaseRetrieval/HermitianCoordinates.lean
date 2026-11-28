module

public import OperatorPhaseRetrieval.HaarTracePairing

@[expose] public section

noncomputable section

open NormedSpace
open scoped InnerProductSpace

namespace OperatorPhaseRetrieval

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- Matrix entries as a Euclidean vector; its norm is the Hilbert--Schmidt norm. -/
def matrixCoefficientEquiv : Matrix ι ι ℂ ≃ₗ[ℂ] EuclideanSpace ℂ (ι × ι) where
  toFun M := WithLp.toLp 2 (fun p => M p.1 p.2)
  invFun x i j := x (i,j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The algebraic identification from Hilbert--Schmidt coordinates to operators.
The norm on its domain is the Euclidean norm; the operator norm is used on the codomain. -/
def hsOperatorEquiv : EuclideanSpace ℂ (ι × ι) ≃ₗ[ℂ]
    (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
  (matrixCoefficientEquiv ι).symm.trans
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv

/-- The real Hilbert space of selfadjoint operators, with the Hilbert--Schmidt norm. -/
def hermitianCoordinates : Submodule ℝ (EuclideanSpace ℂ (ι × ι)) where
  carrier := {x | IsSelfAdjoint (hsOperatorEquiv ι x)}
  zero_mem' := by
    change IsSelfAdjoint (hsOperatorEquiv ι 0)
    rw [map_zero]
    exact IsSelfAdjoint.zero (R := EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
  add_mem' := by
    intro x y hx hy
    change IsSelfAdjoint (hsOperatorEquiv ι x) at hx
    change IsSelfAdjoint (hsOperatorEquiv ι y) at hy
    change IsSelfAdjoint (hsOperatorEquiv ι (x + y))
    rw [map_add]
    exact IsSelfAdjoint.add (R := EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) hx hy
  smul_mem' := by
    intro r x hx
    change IsSelfAdjoint (hsOperatorEquiv ι x) at hx
    change IsSelfAdjoint (hsOperatorEquiv ι (r • x))
    have he : hsOperatorEquiv ι (r • x) = (r : ℂ) • hsOperatorEquiv ι x := by
      rw [← map_smul]
      congr 1
    rw [he]
    exact (show IsSelfAdjoint (r : ℂ) by simp [isSelfAdjoint_iff]).smul hx

instance hermitianCoordinates_finiteDimensional : FiniteDimensional ℝ (hermitianCoordinates ι) :=
  inferInstance

instance hermitianCoordinates_completeSpace : CompleteSpace (hermitianCoordinates ι) :=
  FiniteDimensional.complete ℝ _

def hermitianCoordinateOperator (x : hermitianCoordinates ι) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι := hsOperatorEquiv ι x

theorem hermitianCoordinateOperator_isSelfAdjoint (x : hermitianCoordinates ι) :
    IsSelfAdjoint (hermitianCoordinateOperator ι x) := x.property

/-- Every real tangent functional has a Riesz vector in the Hermitian Hilbert space. -/
theorem hermitianCoordinates_riesz (l : hermitianCoordinates ι →L[ℝ] ℝ) :
    ∃ B : hermitianCoordinates ι, ‖B‖ = ‖l‖ ∧ ∀ A, l A = inner ℝ B A := by
  let B := (InnerProductSpace.toDual ℝ (hermitianCoordinates ι)).symm l
  exact ⟨B, (InnerProductSpace.toDual ℝ (hermitianCoordinates ι)).symm.norm_map l,
    fun A => (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := hermitianCoordinates ι) (x := A) (y := l)).symm⟩

/-- Hermitian coordinates satisfy the conjugate-transpose entry identity. -/
theorem hermitianCoordinates_entry (A : hermitianCoordinates ι) (i j : ι) :
    (starRingEnd ℂ) ((A : EuclideanSpace ℂ (ι × ι)) (j,i)) =
      (A : EuclideanSpace ℂ (ι × ι)) (i,j) := by
  have h : IsSelfAdjoint (hsOperatorEquiv ι (A : EuclideanSpace ℂ (ι × ι))) := A.property
  change IsSelfAdjoint (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
    ((matrixCoefficientEquiv ι).symm (A : EuclideanSpace ℂ (ι × ι)))) at h
  have hM : IsSelfAdjoint ((matrixCoefficientEquiv ι).symm (A : EuclideanSpace ℂ (ι × ι))) := by
    rw [isSelfAdjoint_iff]
    apply EquivLike.injective (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ))
    rw [map_star]
    exact h.star_eq
  exact congrArg (fun M : Matrix ι ι ℂ => M i j) hM.star_eq

theorem trace_hsOperator (x : EuclideanSpace ℂ (ι × ι)) :
    LinearMap.trace ℂ (EuclideanSpace ℂ ι) (hsOperatorEquiv ι x).toLinearMap =
      ∑ i, x (i,i) := by
  change LinearMap.trace ℂ (EuclideanSpace ℂ ι)
    (Matrix.toLin (EuclideanSpace.basisFun ι ℂ).toBasis (EuclideanSpace.basisFun ι ℂ).toBasis
      ((matrixCoefficientEquiv ι).symm x)) = _
  rw [Matrix.trace_toLin_eq]
  rfl

theorem trace_hsOperator_mul (x y : EuclideanSpace ℂ (ι × ι)) :
    LinearMap.trace ℂ (EuclideanSpace ℂ ι) ((hsOperatorEquiv ι x) * (hsOperatorEquiv ι y)).toLinearMap =
      ∑ i, ∑ j, x (i,j) * y (j,i) := by
  change LinearMap.trace ℂ (EuclideanSpace ℂ ι)
    ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) ((matrixCoefficientEquiv ι).symm x)) *
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) ((matrixCoefficientEquiv ι).symm y))).toLinearMap = _
  rw [← map_mul]
  change LinearMap.trace ℂ (EuclideanSpace ℂ ι)
    (Matrix.toLin (EuclideanSpace.basisFun ι ℂ).toBasis (EuclideanSpace.basisFun ι ℂ).toBasis
      (((matrixCoefficientEquiv ι).symm x) * ((matrixCoefficientEquiv ι).symm y))) = _
  rw [Matrix.trace_toLin_eq]
  rfl

/-- The Hilbert--Schmidt real inner product is the real trace pairing. -/
theorem hermitianCoordinates_inner_trace (B A : hermitianCoordinates ι) :
    inner ℝ B A = operatorRealTrace (hermitianCoordinateOperator ι B * hermitianCoordinateOperator ι A) := by
  change inner ℝ (B : EuclideanSpace ℂ (ι × ι)) (A : EuclideanSpace ℂ (ι × ι)) = _
  rw [PiLp.inner_apply]
  simp only [Complex.inner, Fintype.sum_prod_type]
  unfold operatorRealTrace hermitianCoordinateOperator
  rw [trace_hsOperator_mul]
  simp only [Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hermitianCoordinates_entry]
  rw [mul_comm]

/-- The square norm of a Hermitian matrix is the trace of its square. -/
theorem hermitianCoordinates_norm_sq (A : hermitianCoordinates ι) :
    operatorRealTrace ((hermitianCoordinateOperator ι A) ^ 2) = ‖A‖ ^ 2 := by
  rw [pow_two, ← hermitianCoordinates_inner_trace, real_inner_self_eq_norm_sq]

end OperatorPhaseRetrieval

end
