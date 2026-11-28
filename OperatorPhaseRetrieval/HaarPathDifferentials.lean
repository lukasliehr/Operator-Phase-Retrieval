module

public import OperatorPhaseRetrieval.BoundedPathDifferential
public import OperatorPhaseRetrieval.HermitianOperatorBound
public import OperatorPhaseRetrieval.HaarProductPoincare

@[expose] public section

noncomputable section

open MeasureTheory

namespace OperatorPhaseRetrieval

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- Right-translated exponential paths in the six-factor unitary group. -/
def haarSixPath (U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) (A : HermitianSix ι) (t : ℝ) :=
  U * hermitianSixExp ι (t • A)

theorem haarSix_coordinate_hasBoundedPathDifferential (j : Fin 6) :
    HasBoundedPathDifferential (haarSixPath ι)
      (fun U => (U j : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)) 1 := by
  let B : HermitianSix ι →L[ℝ] (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
    (Complex.I • hermitianOperatorCLM ι).comp (PiLp.proj 2 (fun _ : Fin 6 => hermitianCoordinates ι) j)
  let D : (Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) →
      HermitianSix ι →L[ℝ] (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) := fun U =>
    (ContinuousLinearMap.mul ℝ (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (U j)).comp B
  refine ⟨continuous_subtype_val.comp (continuous_apply j), D, ?_, ?_, ?_⟩
  · dsimp [D]
    exact ((ContinuousLinearMap.mul ℝ _).continuous.comp
      (continuous_subtype_val.comp (continuous_apply j))).clm_comp continuous_const
  · intro U A t
    change HasDerivAt (fun s => (U j : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) *
      (hermitianExp ι (s • A j) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι))
      (((U j : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) *
        (hermitianExp ι (t • A j) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)) *
        (Complex.I • hermitianCoordinateOperator ι (A j))) t
    simpa only [mul_assoc] using (hermitianExp_hasDerivAt ι (A j) t).const_mul
      (U j : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
  · intro U A
    change ‖(U j : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) *
      (Complex.I • hermitianCoordinateOperator ι (A j))‖ ≤ 1 * ‖A‖
    calc
      _ ≤ ‖(U j : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)‖ *
          ‖Complex.I • hermitianCoordinateOperator ι (A j)‖ := norm_mul_le _ _
      _ ≤ 1 * ‖Complex.I • hermitianCoordinateOperator ι (A j)‖ :=
        mul_le_mul_of_nonneg_right (unitaryOperator_norm_le _ _) (norm_nonneg _)
      _ = ‖hermitianCoordinateOperator ι (A j)‖ := by rw [norm_smul, Complex.norm_I]; simp
      _ ≤ ‖A j‖ := hermitianCoordinateOperator_norm_le ι _
      _ ≤ 1 * ‖A‖ := by simpa using PiLp.norm_apply_le A j

theorem haarSix_inverse_coordinate_hasBoundedPathDifferential (j : Fin 6) :
    HasBoundedPathDifferential (haarSixPath ι)
      (fun U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι) =>
        (((U j)⁻¹ : HaarUnitary (EuclideanSpace ℂ ι)) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)) 1 := by
  have h := (haarSix_coordinate_hasBoundedPathDifferential ι j).smooth_comp star
    (starL ℝ : (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) ≃L[ℝ]
      (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)).contDiff 1 star_isometry.lipschitzWith
  simpa only [NNReal.coe_one, one_mul, ← Unitary.star_eq_inv, Unitary.coe_star] using h

variable [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Transport an operator to normalized finite L² and regard it as real linear. -/
def finiteL2OperatorTransport : (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) →L[ℝ]
    (L2 (finiteProbability ι) →L[ℝ] L2 (finiteProbability ι)) :=
  (ContinuousLinearMap.restrictScalarsL ℂ (L2 (finiteProbability ι)) (L2 (finiteProbability ι)) ℝ ℝ).comp
    { toLinearMap := (finiteL2Equiv ι ℂ).conjStarAlgEquiv.toAlgEquiv.toLinearEquiv.toLinearMap.restrictScalars ℝ
      cont := (StarAlgEquiv.isometry (finiteL2Equiv ι ℂ).conjStarAlgEquiv).continuous }

omit [DecidableEq ι] in
theorem finiteL2OperatorTransport_norm (T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    ‖finiteL2OperatorTransport ι T‖ = ‖T‖ := by
  change ‖((finiteL2Equiv ι ℂ).conjStarAlgEquiv T).restrictScalars ℝ‖ = _
  rw [ContinuousLinearMap.norm_restrictScalars, StarAlgEquiv.norm_map]

omit [DecidableEq ι] in
theorem finiteL2OperatorTransport_lipschitz : LipschitzWith 1 (finiteL2OperatorTransport ι) := by
  apply LipschitzWith.of_dist_le_mul
  intro S T
  simp only [dist_eq_norm, ← map_sub, finiteL2OperatorTransport_norm, NNReal.coe_one, one_mul, le_refl]

theorem finiteL2Unitary_real_hasBoundedPathDifferential (j : Fin 6) :
    HasBoundedPathDifferential (haarSixPath ι)
      (fun U => (finiteL2Unitary ι (U j)).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ) 1 := by
  have h := (haarSix_coordinate_hasBoundedPathDifferential ι j).smooth_comp
    (finiteL2OperatorTransport ι) (finiteL2OperatorTransport ι).contDiff 1
    (finiteL2OperatorTransport_lipschitz ι)
  have he (U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) :
      finiteL2OperatorTransport ι (U j) =
        (finiteL2Unitary ι (U j)).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ := by
    ext f
    rfl
  simpa only [he, NNReal.coe_one, one_mul] using h

theorem finiteL2Unitary_inverse_real_hasBoundedPathDifferential (j : Fin 6) :
    HasBoundedPathDifferential (haarSixPath ι)
      (fun U => (finiteL2Unitary ι (U j)).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ) 1 := by
  have h := (haarSix_inverse_coordinate_hasBoundedPathDifferential ι j).smooth_comp
    (finiteL2OperatorTransport ι) (finiteL2OperatorTransport ι).contDiff 1
    (finiteL2OperatorTransport_lipschitz ι)
  have he (U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) :
      finiteL2OperatorTransport ι (((U j)⁻¹ : HaarUnitary (EuclideanSpace ℂ ι)) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) =
      (finiteL2Unitary ι (U j)).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ := by
    change (finiteL2Unitary ι ((U j)⁻¹)).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ = _
    rw [finiteL2Unitary_inverse]
  simpa only [he, NNReal.coe_one, one_mul] using h

end OperatorPhaseRetrieval

end
