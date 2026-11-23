import OperatorPhaseRetrieval.HermitianGeometry

noncomputable section

open MeasureTheory NormedSpace
open scoped InnerProductSpace

namespace OperatorPhaseRetrieval

variable (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] in
theorem haarDiagonalPairing_mean (a b : ι → ℝ) :
    (∫ U, haarDiagonalPairing ι a b U
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) =
      (∑ i, a i) * (∑ i, b i) / Fintype.card ι := by
  unfold haarDiagonalPairing
  have hi (i : ι) : Integrable (fun U => b i * haarDiagonal ι a U i)
      (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _) :=
    (continuous_const.mul (haarDiagonal_continuous ι a i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_const_mul, haarDiagonal_mean]
  rw [← Finset.sum_mul]
  ring

omit [DecidableEq ι] in
theorem crossHaarPairing_mean (b c : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι))
    (a β : ι → ℝ) :
    (∫ U, crossHaarPairing ι b c a β U
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) =
      (∑ i, a i) * (∑ i, β i) / Fintype.card ι := by
  have hm := haarInBases_measurePreserving ι b c
  have hf : Measurable (fun U => haarDiagonalPairing ι a β U) := by fun_prop
  have h := integral_map
    (μ := (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure (HaarUnitary (EuclideanSpace ℂ ι))))
    hm.measurable.aemeasurable hf.aestronglyMeasurable
  rw [hm.map_eq] at h
  simp_rw [crossHaarPairing_eq]
  rw [← h]
  exact haarDiagonalPairing_mean ι a β

theorem haar_adjoint_mean (A B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    (∫ U : HaarUnitary (EuclideanSpace ℂ ι),
      operatorRealTrace (B * ((U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) * A *
        ((U⁻¹ : HaarUnitary (EuclideanSpace ℂ ι)) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)))
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) =
      operatorRealTrace A * operatorRealTrace B / Fintype.card ι := by
  obtain ⟨b, a, rfl⟩ := exists_selfAdjoint_diagonal A hA
  obtain ⟨c, β, rfl⟩ := exists_selfAdjoint_diagonal B hB
  simp_rw [operatorRealTrace, trace_conjugate_diagonals]
  rw [crossHaarPairing_mean]
  simp only [basisDiagonal_trace, Complex.re_sum, Complex.ofReal_re]

theorem hermitianConjugate_functional_mean (A : hermitianCoordinates ι)
    (l : hermitianCoordinates ι →L[ℝ] ℝ) :
    (∫ U, l (hermitianConjugate ι U A)
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) =
      operatorRealTrace (hermitianCoordinateOperator ι A) * l (hermitianIdentity ι) / Fintype.card ι := by
  obtain ⟨B, _, hB⟩ := hermitianCoordinates_riesz ι l
  simp_rw [hB]
  rw [real_inner_comm (hermitianIdentity ι) B, hermitianIdentity_inner]
  simp_rw [hermitianCoordinates_inner_trace, hermitianConjugate_operator]
  exact haar_adjoint_mean ι _ _ (hermitianCoordinateOperator_isSelfAdjoint ι A)
    (hermitianCoordinateOperator_isSelfAdjoint ι B)

end OperatorPhaseRetrieval

end
