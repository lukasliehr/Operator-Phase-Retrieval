import OperatorPhaseRetrieval.HaarHermitianMean

noncomputable section

open MeasureTheory NormedSpace
open scoped InnerProductSpace

namespace OperatorPhaseRetrieval

variable (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The covariance retains the orthogonal projection away from the scalar direction. -/
theorem hermitianConjugate_functional_secondMoment (A : hermitianCoordinates ι)
    (ha : operatorRealTrace (hermitianCoordinateOperator ι A) = 0)
    (l : hermitianCoordinates ι →L[ℝ] ℝ) (hn : 1 < Fintype.card ι) :
    (∫ U, (l (hermitianConjugate ι U A)) ^ 2
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) =
      ‖A‖ ^ 2 / ((Fintype.card ι : ℝ) ^ 2 - 1) *
        (‖l‖ ^ 2 - l (hermitianIdentity ι) ^ 2 / Fintype.card ι) := by
  obtain ⟨B, hBnorm, hB⟩ := hermitianCoordinates_riesz ι l
  have hid : l (hermitianIdentity ι) = operatorRealTrace (hermitianCoordinateOperator ι B) := by
    rw [hB, real_inner_comm (hermitianIdentity ι) B, hermitianIdentity_inner]
  rw [hid]
  simp_rw [hB, hermitianCoordinates_inner_trace, hermitianConjugate_operator]
  rw [haar_adjoint_secondMoment (hermitianCoordinateOperator ι A) (hermitianCoordinateOperator ι B)
    (hermitianCoordinateOperator_isSelfAdjoint ι A) (hermitianCoordinateOperator_isSelfAdjoint ι B) ha hn,
    hermitianCoordinates_norm_sq, hermitianCoordinates_norm_sq, hBnorm]

/-- The exact second moment separates the scalar and trace-zero directions. -/
theorem hermitianConjugate_functional_secondMoment_general (A : hermitianCoordinates ι)
    (l : hermitianCoordinates ι →L[ℝ] ℝ) (hn : 1 < Fintype.card ι) :
    (∫ U, (l (hermitianConjugate ι U A)) ^ 2
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) =
      ‖hermitianCenter ι A‖ ^ 2 / ((Fintype.card ι : ℝ) ^ 2 - 1) *
        (‖l‖ ^ 2 - l (hermitianIdentity ι) ^ 2 / Fintype.card ι) +
      (operatorRealTrace (hermitianCoordinateOperator ι A) / Fintype.card ι *
        l (hermitianIdentity ι)) ^ 2 := by
  let μ : Measure (HaarUnitary (EuclideanSpace ℂ ι)) :=
    (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)
  let c := operatorRealTrace (hermitianCoordinateOperator ι A) / Fintype.card ι
  let m := c * l (hermitianIdentity ι)
  let f := fun U => l (hermitianConjugate ι U (hermitianCenter ι A))
  have hc : Continuous f := l.continuous.comp (hermitianConjugate_continuous ι _)
  have hi : Integrable f μ := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun U => f U ^ 2) μ :=
    (hc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmean : (∫ U, f U ∂μ) = 0 := by
    dsimp [f, μ]
    rw [hermitianConjugate_functional_mean, hermitianCenter_trace, zero_mul, zero_div]
  have he (U : HaarUnitary (EuclideanSpace ℂ ι)) : l (hermitianConjugate ι U A) = f U + m := by
    have hdec : A = hermitianCenter ι A + c • hermitianIdentity ι := by
      dsimp [hermitianCenter, c]
      abel
    calc
      l (hermitianConjugate ι U A) = l (hermitianConjugateCLM ι U
        (hermitianCenter ι A + c • hermitianIdentity ι)) := by rw [← hdec]; rfl
      _ = f U + m := by
        simp only [map_add, map_smul, hermitianConjugateCLM_apply, hermitianConjugate_identity,
          smul_eq_mul, f, m]
  have hexpand : (∫ U, (l (hermitianConjugate ι U A)) ^ 2 ∂μ) =
      (∫ U, f U ^ 2 ∂μ) + m ^ 2 := by
    calc
      _ = ∫ U, (f U ^ 2 + (2*m)*f U) + m ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards with U
        rw [he]
        ring
      _ = _ := by
        rw [integral_add (f := fun U => f U ^ 2 + (2*m)*f U)
          (hi2.add (hi.const_mul _)) (integrable_const _),
          integral_add hi2 (hi.const_mul (2*m)), integral_const_mul, hmean]
        simp
  rw [hexpand]
  rw [hermitianConjugate_functional_secondMoment ι _ (hermitianCenter_trace ι A) l hn]

end OperatorPhaseRetrieval

end
