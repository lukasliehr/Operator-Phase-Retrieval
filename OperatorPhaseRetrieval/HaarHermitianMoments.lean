module

public import OperatorPhaseRetrieval.HermitianCoordinates

@[expose] public section

noncomputable section

open MeasureTheory NormedSpace
open scoped InnerProductSpace

namespace OperatorPhaseRetrieval

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

theorem hsOperatorEquiv_apply_symm (T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    hsOperatorEquiv ι ((hsOperatorEquiv ι).symm T) = T :=
  (hsOperatorEquiv ι).apply_symm_apply T

/-- Conjugation acts on the Hilbert space of Hermitian coefficient vectors. -/
def hermitianConjugate (U : HaarUnitary (EuclideanSpace ℂ ι)) (A : hermitianCoordinates ι) :
    hermitianCoordinates ι :=
  ⟨(hsOperatorEquiv ι).symm ((U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) *
      hermitianCoordinateOperator ι A *
      ((U⁻¹ : HaarUnitary (EuclideanSpace ℂ ι)) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)), by
    change IsSelfAdjoint (hsOperatorEquiv ι ((hsOperatorEquiv ι).symm _))
    rw [hsOperatorEquiv_apply_symm]
    exact (hermitianCoordinateOperator_isSelfAdjoint ι A).conjugate
      (U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)⟩

theorem hermitianConjugate_operator (U : HaarUnitary (EuclideanSpace ℂ ι)) (A : hermitianCoordinates ι) :
    hermitianCoordinateOperator ι (hermitianConjugate ι U A) =
      (U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) * hermitianCoordinateOperator ι A *
        ((U⁻¹ : HaarUnitary (EuclideanSpace ℂ ι)) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) := by
  change hsOperatorEquiv ι ((hsOperatorEquiv ι).symm _) = _
  rw [hsOperatorEquiv_apply_symm]

@[fun_prop]
theorem hermitianConjugate_continuous (A : hermitianCoordinates ι) :
    Continuous (fun U => hermitianConjugate ι U A) := by
  apply Continuous.subtype_mk
  change Continuous (fun U : HaarUnitary (EuclideanSpace ℂ ι) =>
    (hsOperatorEquiv ι).symm ((U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) *
      hermitianCoordinateOperator ι A *
        ((U⁻¹ : HaarUnitary (EuclideanSpace ℂ ι)) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)))
  exact (hsOperatorEquiv ι).symm.toContinuousLinearEquiv.continuous.comp
    ((continuous_subtype_val.mul continuous_const).mul
      (ContinuousLinearMap.adjoint.continuous.comp continuous_subtype_val))

/-- Haar covariance controls any real linear tangent functional. -/
theorem hermitianConjugate_functional_secondMoment_le [Nonempty ι]
    (A : hermitianCoordinates ι) (ha : operatorRealTrace (hermitianCoordinateOperator ι A) = 0)
    (l : hermitianCoordinates ι →L[ℝ] ℝ) (hn : 1 < Fintype.card ι) :
    (∫ U, (l (hermitianConjugate ι U A)) ^ 2
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) ≤
      ‖A‖ ^ 2 / ((Fintype.card ι : ℝ) ^ 2 - 1) * ‖l‖ ^ 2 := by
  obtain ⟨B, hBnorm, hB⟩ := hermitianCoordinates_riesz ι l
  simp_rw [hB, hermitianCoordinates_inner_trace, hermitianConjugate_operator]
  rw [haar_adjoint_secondMoment (hermitianCoordinateOperator ι A) (hermitianCoordinateOperator ι B)
    (hermitianCoordinateOperator_isSelfAdjoint ι A) (hermitianCoordinateOperator_isSelfAdjoint ι B) ha hn]
  rw [hermitianCoordinates_norm_sq, hermitianCoordinates_norm_sq, hBnorm]
  apply mul_le_mul_of_nonneg_left
  · exact sub_le_self _ (by positivity)
  · have hnR : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hn
    exact div_nonneg (sq_nonneg _) (by nlinarith)

end OperatorPhaseRetrieval

end
