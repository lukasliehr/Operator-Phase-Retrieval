import OperatorPhaseRetrieval.AveragedPathEnergy
import OperatorPhaseRetrieval.BoundedHaarDirections
import OperatorPhaseRetrieval.HermitianUnitaryPaths

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace OperatorPhaseRetrieval

variable (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Poincaré inequality on the actual unitary Haar probability. The derivative is
specified intrinsically along right-translated Hermitian exponential paths. -/
theorem haarUnitary_poincare
    (F : HaarUnitary (EuclideanSpace ℂ ι) → ℝ) (hF : Continuous F)
    (D : HaarUnitary (EuclideanSpace ℂ ι) → hermitianCoordinates ι →L[ℝ] ℝ)
    (hD : Continuous D)
    (hderiv : ∀ U A t, t ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (fun s => F (U * hermitianExp ι (s • A)))
        (D (U * hermitianExp ι (t • A)) A) t) :
    variance F (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _) ≤
      (6 * Real.pi ^ 2 / Fintype.card ι) *
        ∫ U, ‖D U‖ ^ 2 ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _) := by
  let μ : Measure (HaarUnitary (EuclideanSpace ℂ ι)) :=
    (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)
  calc
    _ ≤ ((12 * Real.pi ^ 2 / Fintype.card ι) / 2) * ∫ U, ‖D U‖ ^ 2 ∂μ := by
      apply variance_le_of_averaged_paths μ F hF D hD
      intro W
      obtain ⟨A, hA, hnorm, htrace⟩ := exists_balanced_hermitian_log ι W
      refine ⟨fun Z => hermitianConjugate ι Z A,
        fun Z t => hermitianExp ι (t • hermitianConjugate ι Z A),
        hermitianConjugate_continuous ι A, ?_, ?_, ?_, ?_, ?_⟩
      · exact (hermitianExp_continuous ι).comp
          (continuous_snd.smul ((hermitianConjugate_continuous ι A).comp continuous_fst))
      · intro Z
        simp only [zero_smul, hermitianExp_zero]
      · intro Z
        simp only [one_smul, hermitianExp_conjugate, hA]
      · intro U Z t ht
        exact hderiv U (hermitianConjugate ι Z A) t ht
      · intro U
        exact hermitianConjugate_secondMoment_le_balanced ι A hnorm htrace (D U)
    _ = _ := by ring

end OperatorPhaseRetrieval

end
