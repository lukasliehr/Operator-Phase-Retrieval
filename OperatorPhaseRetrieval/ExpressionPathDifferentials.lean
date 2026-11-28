module

public import OperatorPhaseRetrieval.HaarPathDifferentials
public import OperatorPhaseRetrieval.FiniteL2SmoothMaps
public import OperatorPhaseRetrieval.TransformedHaarExpressions
public import OperatorPhaseRetrieval.FiniteCoordinateBounds

@[expose] public section

noncomputable section

open MeasureTheory
open scoped NNReal

namespace OperatorPhaseRetrieval

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

variable (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

omit [DecidableEq ι] [Nonempty ι] [MeasurableSingletonClass ι] in
theorem finiteL2Isometry_real_norm_le (V : L2 (finiteProbability ι) ≃ₗᵢ[ℂ] L2 (finiteProbability ι)) :
    ‖V.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  simp

/-- Smooth transformed expressions have the same dimension-independent derivative
bound as their original operator-family Lipschitz bound. -/
theorem finiteTransformedExpression_hasBoundedPathDifferential
    (ψ : ℂ → ℂ) (hψ : LipschitzWith 1 ψ) (hzero : ψ 0 = 0)
    (hsmooth : ContDiff ℝ ⊤ ψ) (t : StabilityExpression) :
    HasBoundedPathDifferential (haarSixPath ι)
      (fun U => StabilityExpression.transformedEval ψ hψ hzero (finiteHaarModel ι U) t)
      t.lipBound := by
  induction t with
  | one => exact HasBoundedPathDifferential.const _
  | seed =>
    have h := (finiteL2Unitary_real_hasBoundedPathDifferential ι 0).clm_apply
      (HasBoundedPathDifferential.const (Lp.const 2 (finiteProbability ι) (1 : ℂ)))
      (fun U => finiteL2Isometry_real_norm_le ι _) (R := 1)
      (fun _ => by simp [Lp.norm_const]) (by norm_num)
    simpa [StabilityExpression.transformedEval, finiteHaarModel, StabilityExpression.lipBound] using h
  | add s t hs ht => exact hs.add ht
  | smul a b t ht =>
    have hlip : LipschitzWith ‖rationalComplex a b‖₊
        (fun f : L2 (finiteProbability ι) => rationalComplex a b • f) := by
      apply LipschitzWith.of_dist_le_mul
      intro f g
      simp [dist_eq_norm, ← smul_sub, norm_smul]
    exact ht.smooth_comp _ (contDiff_id.const_smul _) _ hlip
  | conj t ht =>
    have hlip : LipschitzWith 1 (conjugateL2 : L2 (finiteProbability ι) → L2 (finiteProbability ι)) := by
      apply LipschitzWith.of_dist_le_mul
      intro f g
      simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using conjugateL2_sub_le f g
    simpa [StabilityExpression.transformedEval, StabilityExpression.lipBound] using
      ht.smooth_comp conjugateL2 (finiteL2_conjugate_contDiff ι) 1 hlip
  | modulus t ht =>
    have hlip : LipschitzWith 1 (fun f : L2 (finiteProbability ι) => hψ.compLp hzero f) := by
      apply LipschitzWith.of_dist_le_mul
      intro f g
      simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using hψ.norm_compLp_sub_le hzero f g
    simpa [StabilityExpression.transformedEval, StabilityExpression.lipBound] using
      ht.smooth_comp _ (finiteL2_compLp_contDiff ι ψ hψ hzero hsmooth) 1 hlip
  | apply j inverse t ht =>
    have hb U := StabilityExpression.transformedEval_norm_le ψ hψ hzero (finiteHaarModel ι U) t
    cases inverse with
    | false =>
      have h := (finiteL2Unitary_real_hasBoundedPathDifferential ι j.succ).clm_apply ht
        (fun U => finiteL2Isometry_real_norm_le ι _) hb (by norm_num)
      simpa [StabilityExpression.transformedEval, finiteHaarModel, unitaryAction, StabilityExpression.lipBound, add_comm] using h
    | true =>
      have h := (finiteL2Unitary_inverse_real_hasBoundedPathDifferential ι j.succ).clm_apply ht
        (fun U => finiteL2Isometry_real_norm_le ι _) hb (by norm_num)
      simpa [StabilityExpression.transformedEval, finiteHaarModel, unitaryAction, StabilityExpression.lipBound, add_comm] using h

/-- Coordinate evaluation as a real continuous linear map. -/
def finiteL2CoordinateCLM (i : ι) : L2 (finiteProbability ι) →L[ℝ] ℂ :=
  (Real.sqrt (Fintype.card ι) • (PiLp.proj 2 (fun _ : ι => ℂ) i).comp
    (finiteL2Equiv ι ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ

omit [DecidableEq ι] in
theorem finiteL2CoordinateCLM_apply (i : ι) (f : L2 (finiteProbability ι)) :
    finiteL2CoordinateCLM ι i f = f i := by
  change Real.sqrt (Fintype.card ι) • ((finiteL2Equiv ι ℂ).symm f) i = f i
  simpa only [(finiteL2Equiv ι ℂ).apply_symm_apply] using
    (finiteL2Equiv_apply ι ℂ ((finiteL2Equiv ι ℂ).symm f) i).symm

omit [DecidableEq ι] in
theorem finiteL2CoordinateCLM_norm_le (i : ι) :
    ‖finiteL2CoordinateCLM ι i‖ ≤ Real.sqrt (Fintype.card ι) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro f
  rw [finiteL2CoordinateCLM_apply]
  exact finiteL2_coordinate_norm_le ι f i

theorem finiteTransformedExpression_coordinate_hasBoundedPathDifferential
    (ψ : ℂ → ℂ) (hψ : LipschitzWith 1 ψ) (hzero : ψ 0 = 0)
    (hsmooth : ContDiff ℝ ⊤ ψ) (t : StabilityExpression) (i : ι) :
    HasBoundedPathDifferential (haarSixPath ι)
      (fun U => StabilityExpression.transformedEval ψ hψ hzero (finiteHaarModel ι U) t i)
      (Real.sqrt (Fintype.card ι) * t.lipBound) := by
  have h := ((finiteTransformedExpression_hasBoundedPathDifferential ι ψ hψ hzero hsmooth t).clm_comp
    (finiteL2CoordinateCLM ι i)).mono
      (mul_le_mul_of_nonneg_right (finiteL2CoordinateCLM_norm_le ι i) (NNReal.coe_nonneg _))
  simpa only [finiteL2CoordinateCLM_apply] using h

end OperatorPhaseRetrieval

end
