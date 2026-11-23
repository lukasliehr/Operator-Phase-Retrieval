import OperatorPhaseRetrieval.BoundedHaarDirections

noncomputable section

open MeasureTheory ProbabilityTheory NormedSpace

namespace OperatorPhaseRetrieval

variable (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Subtracting the squared mean leaves precisely the trace-zero covariance. -/
theorem hermitianConjugate_functional_variance (A : hermitianCoordinates ι)
    (l : hermitianCoordinates ι →L[ℝ] ℝ) (hn : 1 < Fintype.card ι) :
    variance (fun U => l (hermitianConjugate ι U A))
      (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _) =
      ‖hermitianCenter ι A‖ ^ 2 / ((Fintype.card ι : ℝ) ^ 2 - 1) *
        (‖l‖ ^ 2 - l (hermitianIdentity ι) ^ 2 / Fintype.card ι) := by
  have hc : Continuous (fun U => l (hermitianConjugate ι U A)) :=
    l.continuous.comp (hermitianConjugate_continuous ι A)
  rw [variance_eq_sub (hc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  simp only [Pi.pow_apply]
  rw [hermitianConjugate_functional_secondMoment_general ι A l hn,
    hermitianConjugate_functional_mean]
  ring

/-- The traceless covariance coefficient for a logarithm of norm at most `3 pi`. -/
theorem hermitian_balanced_covariance_coefficient_le (A : hermitianCoordinates ι)
    (hA : ‖hermitianCoordinateOperator ι A‖ ≤ 3 * Real.pi) (hn : 1 < Fintype.card ι) :
    ‖hermitianCenter ι A‖ ^ 2 / ((Fintype.card ι : ℝ) ^ 2 - 1) ≤
      12 * Real.pi ^ 2 / Fintype.card ι := by
  have hnR : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  apply (div_le_iff₀ (show 0 < (Fintype.card ι : ℝ) ^ 2 - 1 by nlinarith)).mpr
  exact (hermitianCenter_norm_sq_le ι A).trans
    (hermitian_balanced_norm_sq_le_covariance ι A hA hn)

theorem hermitianConjugate_variance_le_balanced (A : hermitianCoordinates ι)
    (hA : ‖hermitianCoordinateOperator ι A‖ ≤ 3 * Real.pi)
    (l : hermitianCoordinates ι →L[ℝ] ℝ) (hn : 1 < Fintype.card ι) :
    variance (fun U => l (hermitianConjugate ι U A))
      (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _) ≤
      (12 * Real.pi ^ 2 / Fintype.card ι) *
        (‖l‖ ^ 2 - l (hermitianIdentity ι) ^ 2 / Fintype.card ι) := by
  rw [hermitianConjugate_functional_variance ι A l hn]
  apply mul_le_mul_of_nonneg_right (hermitian_balanced_covariance_coefficient_le ι A hA hn)
  apply sub_nonneg.mpr
  exact (div_le_iff₀ (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card ι)).mpr
    (hermitianFunctional_identity_sq_le ι l)

end OperatorPhaseRetrieval

end
