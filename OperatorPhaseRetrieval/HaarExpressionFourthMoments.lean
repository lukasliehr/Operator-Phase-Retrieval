import OperatorPhaseRetrieval.ExpressionPathDifferentials
import OperatorPhaseRetrieval.ExpressionApproximation
import OperatorPhaseRetrieval.HaarSmoothFourthMoments

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal

namespace OperatorPhaseRetrieval

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

variable (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem finiteTransformedExpression_coordinate_fourthMoment_le
    (hn : 1 < Fintype.card ι) (ψ : ℂ → ℂ) (hψ : LipschitzWith 1 ψ) (hzero : ψ 0 = 0)
    (hsmooth : ContDiff ℝ ⊤ ψ) (t : StabilityExpression) (i : ι) :
    (∫ U, ‖StabilityExpression.transformedEval ψ hψ hzero (finiteHaarModel ι U) t i‖ ^ 4
      ∂(haarSixProbability ι : Measure _)) ≤ 8 * (t.radius : ℝ) ^ 4 + 2304 * (t.lipBound : ℝ) ^ 4 := by
  obtain ⟨hF, D, hD, hderiv, hbound⟩ :=
    finiteTransformedExpression_coordinate_hasBoundedPathDifferential ι ψ hψ hzero hsmooth t i
  apply haarSix_smooth_fourthMoment_paper_bound ι hn _ hF D hD
    (fun U A s _ => hderiv U A s) _ _ (NNReal.coe_nonneg _)
    (finiteTransformedExpression_coordinate_secondMoment_le ι ψ hψ hzero t i)
  intro U
  exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) (hbound U)

/-- The coordinate fourth-moment bound for the actual, nonsmooth expressions.
The proof uses smooth modulus approximation and dominated convergence. -/
theorem finiteExpression_coordinate_fourthMoment_le (t : StabilityExpression) (i : ι) :
    (∫ U, ‖t.eval (finiteHaarModel ι U) i‖ ^ 4 ∂(haarSixProbability ι : Measure _)) ≤
      8 * (t.radius : ℝ) ^ 4 + 2304 * (t.lipBound : ℝ) ^ 4 := by
  by_cases hn : 1 < Fintype.card ι
  · let ε (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
    have hε (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
    let F (k : ℕ) (U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) : L2 (finiteProbability ι) :=
      StabilityExpression.transformedEval (smoothModulus (ε k)) (smoothModulus_lipschitz (ε k))
        (smoothModulus_zero (hε k).le) (finiteHaarModel ι U) t
    have hFc (k : ℕ) : Continuous (F k) := finiteTransformedExpression_continuous ι _ _ _ t
    have hFn (k : ℕ) (U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) : ‖F k U‖ ≤ t.radius :=
      StabilityExpression.transformedEval_norm_le _ _ _ _ t
    have hlim (U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) :
        Tendsto (fun k => F k U) atTop (𝓝 (t.eval (finiteHaarModel ι U))) := by
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      apply squeeze_zero (fun k => norm_nonneg _)
        (fun k => StabilityExpression.smooth_transformedEval_error_le (ε k) (hε k).le _ t)
      simpa only [mul_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (t.approximationWeight : ℝ)
    have hi := tendsto_integral_of_dominated_convergence
      (μ := (haarSixProbability ι : Measure _))
      (F := fun k U => ‖F k U i‖ ^ 4)
      (f := fun U => ‖t.eval (finiteHaarModel ι U) i‖ ^ 4)
      (fun _ => (Real.sqrt (Fintype.card ι) * (t.radius : ℝ)) ^ 4)
      (fun k => (((finiteL2_coordinate_continuous ι i).comp (hFc k)).norm.pow 4).aestronglyMeasurable)
      (integrable_const _) ?_ ?_
    · apply le_of_tendsto hi
      exact Filter.Eventually.of_forall fun k =>
        finiteTransformedExpression_coordinate_fourthMoment_le ι hn _ _ _
          (smoothModulus_contDiff (hε k)) t i
    · intro k
      exact Filter.Eventually.of_forall fun U => by
        rw [Real.norm_of_nonneg (by positivity)]
        apply pow_le_pow_left₀ (norm_nonneg _)
        exact (finiteL2_coordinate_norm_le ι (F k U) i).trans
          (mul_le_mul_of_nonneg_left (hFn k U) (Real.sqrt_nonneg _))
    · exact Filter.Eventually.of_forall fun U =>
        (((finiteL2_coordinate_continuous ι i).tendsto _).comp (hlim U)).norm.pow 4
  · have hn1 : Fintype.card ι = 1 := by have := Fintype.card_pos (α := ι); omega
    have hb (U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) :
        ‖t.eval (finiteHaarModel ι U) i‖ ≤ t.radius := by
      have h := finiteL2_coordinate_norm_le ι (t.eval (finiteHaarModel ι U)) i
      simp only [hn1, Nat.cast_one, Real.sqrt_one, one_mul] at h
      exact h.trans (t.eval_norm_le _)
    calc
      _ ≤ ∫ _U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι), (t.radius : ℝ) ^ 4
          ∂(haarSixProbability ι : Measure _) :=
        integral_mono (finiteExpression_coordinate_norm_pow_integrable ι t i 4)
          (integrable_const _) (fun U => pow_le_pow_left₀ (norm_nonneg _) (hb U) 4)
      _ = (t.radius : ℝ) ^ 4 := by simp
      _ ≤ _ := by nlinarith [pow_nonneg (NNReal.coe_nonneg t.radius) 4, pow_nonneg (NNReal.coe_nonneg t.lipBound) 4]

end OperatorPhaseRetrieval

end
