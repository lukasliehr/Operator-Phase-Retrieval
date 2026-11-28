module

public import OperatorPhaseRetrieval.HermitianCentering
public import OperatorPhaseRetrieval.HaarHermitianMoments

@[expose] public section

noncomputable section

open MeasureTheory NormedSpace
open scoped InnerProductSpace

namespace OperatorPhaseRetrieval

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

def hermitianOperatorCLM : hermitianCoordinates ι →L[ℝ]
    (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
  ((hsOperatorEquiv ι).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).comp
    (hermitianCoordinates ι).subtypeL

@[simp] theorem hermitianOperatorCLM_apply (A : hermitianCoordinates ι) :
    hermitianOperatorCLM ι A = hermitianCoordinateOperator ι A := rfl

theorem hermitianCoordinateOperator_injective : Function.Injective (hermitianCoordinateOperator ι) := by
  intro A B h
  exact Subtype.ext ((hsOperatorEquiv ι).injective h)

theorem hermitianConjugate_operator_eq (U : HaarUnitary (EuclideanSpace ℂ ι))
    (A : hermitianCoordinates ι) :
    hermitianCoordinateOperator ι (hermitianConjugate ι U A) =
      (Unitary.linearIsometryEquiv U).conjStarAlgEquiv (hermitianCoordinateOperator ι A) := by
  exact (hsOperatorEquiv ι).apply_symm_apply _

def hermitianConjugateCLM (U : HaarUnitary (EuclideanSpace ℂ ι)) :
    hermitianCoordinates ι →L[ℝ] hermitianCoordinates ι :=
  LinearMap.toContinuousLinearMap
    { toFun := hermitianConjugate ι U
      map_add' := by
        intro A B
        apply hermitianCoordinateOperator_injective ι
        rw [hermitianConjugate_operator_eq]
        change (Unitary.linearIsometryEquiv U).conjStarAlgEquiv (hermitianOperatorCLM ι (A+B)) =
          hermitianOperatorCLM ι (hermitianConjugate ι U A + hermitianConjugate ι U B)
        rw [map_add, map_add, map_add]
        simp only [hermitianOperatorCLM_apply, hermitianConjugate_operator_eq]
      map_smul' := by
        intro r A
        apply hermitianCoordinateOperator_injective ι
        rw [hermitianConjugate_operator_eq]
        change (Unitary.linearIsometryEquiv U).conjStarAlgEquiv (hermitianOperatorCLM ι (r • A)) =
          hermitianOperatorCLM ι (r • hermitianConjugate ι U A)
        rw [(hermitianOperatorCLM ι).map_smul, (hermitianOperatorCLM ι).map_smul,
          LinearMapClass.map_smul_of_tower]
        simp only [hermitianOperatorCLM_apply, hermitianConjugate_operator_eq] }

@[simp] theorem hermitianConjugateCLM_apply (U : HaarUnitary (EuclideanSpace ℂ ι))
    (A : hermitianCoordinates ι) : hermitianConjugateCLM ι U A = hermitianConjugate ι U A := rfl

theorem hermitianConjugate_identity (U : HaarUnitary (EuclideanSpace ℂ ι)) :
    hermitianConjugate ι U (hermitianIdentity ι) = hermitianIdentity ι := by
  apply hermitianCoordinateOperator_injective ι
  rw [hermitianConjugate_operator_eq]
  rw [hermitianIdentity_operator, map_one]

omit [DecidableEq ι] in
theorem operatorRealTrace_unitary_conjugate (U : HaarUnitary (EuclideanSpace ℂ ι))
    (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    operatorRealTrace ((Unitary.linearIsometryEquiv U).conjStarAlgEquiv A) = operatorRealTrace A := by
  exact congrArg Complex.re (LinearMap.trace_conj' A.toLinearMap
    (Unitary.linearIsometryEquiv U).toLinearEquiv)

theorem hermitianConjugate_trace (U : HaarUnitary (EuclideanSpace ℂ ι))
    (A : hermitianCoordinates ι) :
    operatorRealTrace (hermitianCoordinateOperator ι (hermitianConjugate ι U A)) =
      operatorRealTrace (hermitianCoordinateOperator ι A) := by
  rw [hermitianConjugate_operator_eq]
  exact operatorRealTrace_unitary_conjugate ι U _

theorem hermitianConjugate_norm (U : HaarUnitary (EuclideanSpace ℂ ι))
    (A : hermitianCoordinates ι) : ‖hermitianConjugate ι U A‖ = ‖A‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← hermitianCoordinates_norm_sq, ← hermitianCoordinates_norm_sq]
  rw [hermitianConjugate_operator_eq]
  rw [← map_pow, operatorRealTrace_unitary_conjugate]

/-- The Hilbert--Schmidt square norm is at most dimension times operator norm squared. -/
theorem hermitianCoordinates_norm_sq_le (A : hermitianCoordinates ι) :
    ‖A‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ‖hermitianCoordinateOperator ι A‖ ^ 2 := by
  obtain ⟨b, a, ha⟩ := exists_selfAdjoint_diagonal
    (hermitianCoordinateOperator ι A) (hermitianCoordinateOperator_isSelfAdjoint ι A)
  have hb (i : ι) : |a i| ≤ ‖hermitianCoordinateOperator ι A‖ := by
    have h := (hermitianCoordinateOperator ι A).le_opNorm (b i)
    rw [← ha, basisDiagonal_apply_basis, norm_smul, b.norm_eq_one, mul_one, mul_one] at h
    simpa only [Complex.norm_real, Real.norm_eq_abs, ha] using h
  conv_lhs => rw [← hermitianCoordinates_norm_sq, ← ha, operatorRealTrace_basisDiagonal_sq]
  calc
    ∑ i, a i ^ 2 ≤ ∑ _i : ι, ‖hermitianCoordinateOperator ι A‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (a i)) (norm_nonneg _)).mpr (hb i)
    _ = _ := by simp

end OperatorPhaseRetrieval

end
