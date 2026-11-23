import OperatorPhaseRetrieval.HaarDiagonalCovariance
import OperatorPhaseRetrieval.SpectralCoordinates

noncomputable section

open MeasureTheory NormedSpace
open scoped InnerProductSpace

namespace OperatorPhaseRetrieval

variable (ι : Type*) [Fintype ι]

/-- Express a Haar operator between two independently chosen orthonormal bases. -/
def haarInBases (b c : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι))
    (U : HaarUnitary (EuclideanSpace ℂ ι)) : HaarUnitary (EuclideanSpace ℂ ι) :=
  Unitary.linearIsometryEquiv.symm b.repr * U * Unitary.linearIsometryEquiv.symm c.repr.symm

theorem haarInBases_apply (b c : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι))
    (U : HaarUnitary (EuclideanSpace ℂ ι)) (x : EuclideanSpace ℂ ι) :
    (haarInBases ι b c U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) x =
      b.repr ((U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (c.repr.symm x)) := rfl

theorem haarInBases_measurePreserving (b c : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) :
    MeasurePreserving (haarInBases ι b c)
      (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)
      (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _) := by
  exact (measurePreserving_mul_right _ (Unitary.linearIsometryEquiv.symm c.repr.symm)).comp
    (measurePreserving_mul_left _ (Unitary.linearIsometryEquiv.symm b.repr))

theorem haarEntry_inBases (b c : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι))
    (U : HaarUnitary (EuclideanSpace ℂ ι)) (i j : ι) :
    haarEntry ι (haarInBases ι b c U) i j =
      inner ℂ (b i) ((U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (c j)) := by
  classical
  unfold haarEntry
  rw [haarInBases_apply]
  have hc : c.repr.symm (EuclideanSpace.basisFun ι ℂ j) = c j := by
    apply c.repr.injective
    simp [c.repr_self, EuclideanSpace.basisFun_apply]
  rw [hc, b.repr_apply_apply]

/-- Trace-pairing coordinates in two arbitrary orthonormal bases. -/
def crossHaarPairing (b c : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι))
    (a β : ι → ℝ) (U : HaarUnitary (EuclideanSpace ℂ ι)) : ℝ :=
  ∑ i, ∑ j, β i * a j *
    ‖inner ℂ (b i) ((U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (c j))‖ ^ 2

theorem crossHaarPairing_eq (b c : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι))
    (a β : ι → ℝ) (U : HaarUnitary (EuclideanSpace ℂ ι)) :
    crossHaarPairing ι b c a β U = haarDiagonalPairing ι a β (haarInBases ι b c U) := by
  simp only [crossHaarPairing, haarDiagonalPairing, haarDiagonal,
    Finset.mul_sum, haarEntry_inBases, mul_assoc]

/-- The proved Haar covariance is independent of the two chosen eigenbases. -/
theorem crossHaarPairing_covariance [Nonempty ι]
    (b c : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι))
    (a α β δ : ι → ℝ) (ha : ∑ j, a j = 0) (hn : 1 < Fintype.card ι) :
    (∫ U, crossHaarPairing ι b c a β U * crossHaarPairing ι b c α δ U
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) =
    ((∑ j, a j * α j) / ((Fintype.card ι : ℝ) ^ 2 - 1)) *
      ((∑ i, β i * δ i) - (∑ i, β i) * (∑ i, δ i) / Fintype.card ι) := by
  have hm := haarInBases_measurePreserving ι b c
  have hf : Measurable (fun U => haarDiagonalPairing ι a β U * haarDiagonalPairing ι α δ U) := by
    fun_prop
  have h := integral_map
    (μ := (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure (HaarUnitary (EuclideanSpace ℂ ι))))
    hm.measurable.aemeasurable hf.aestronglyMeasurable
  rw [hm.map_eq] at h
  simp_rw [crossHaarPairing_eq]
  rw [← h]
  exact haarDiagonalPairing_covariance ι a α β δ ha hn

end OperatorPhaseRetrieval

end
