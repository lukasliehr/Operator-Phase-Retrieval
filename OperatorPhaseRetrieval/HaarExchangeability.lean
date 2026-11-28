module

public import OperatorPhaseRetrieval.HaarConjugation

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OperatorPhaseRetrieval

variable (ι : Type*) [Fintype ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The coordinate laws of every expression are invariant under permutations. -/
theorem finiteExpression_coordinate_law_permutation (p : Equiv.Perm ι)
    (t : StabilityExpression) (i : ι) :
    (haarSixProbability ι : Measure _).map (fun U => t.eval (finiteHaarModel ι U) i) =
    (haarSixProbability ι : Measure _).map (fun U => t.eval (finiteHaarModel ι U) (p.symm i)) := by
  have hc := haarSixConjugate_measurePreserving ι (permutationHaarUnitary ι p)
  have he := congrArg (fun μ : Measure (Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) =>
    μ.map (fun U => t.eval (finiteHaarModel ι U) i)) hc.map_eq
  rw [Measure.map_map (finiteExpression_coordinate_continuous ι t i).measurable hc.measurable] at he
  simpa only [Function.comp_def, finiteExpression_conjugate_permutation,
    finiteL2Unitary_permutation_apply] using he.symm

/-- In particular, any two coordinates of an expression have the same law. -/
theorem finiteExpression_coordinate_identDistrib (t : StabilityExpression) (i j : ι) :
    IdentDistrib (fun U => t.eval (finiteHaarModel ι U) i)
      (fun U => t.eval (finiteHaarModel ι U) j)
      (haarSixProbability ι : Measure _) (haarSixProbability ι : Measure _) := by
  classical
  refine ⟨(finiteExpression_coordinate_continuous ι t i).measurable.aemeasurable,
    (finiteExpression_coordinate_continuous ι t j).measurable.aemeasurable, ?_⟩
  simpa only [Equiv.symm_swap, Equiv.swap_apply_left] using
    finiteExpression_coordinate_law_permutation ι (Equiv.swap i j) t i

theorem finiteExpression_coordinate_norm_pow_integrable (t : StabilityExpression) (i : ι) (p : ℕ) :
    Integrable (fun U => ‖t.eval (finiteHaarModel ι U) i‖ ^ p) (haarSixProbability ι : Measure _) :=
  ((finiteExpression_coordinate_continuous ι t i).norm.pow p).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Exchangeability turns the deterministic normalized L² bound into a
uniform second-moment bound for every coordinate. -/
theorem finiteExpression_coordinate_secondMoment_le (t : StabilityExpression) (i : ι) :
    (∫ U, ‖t.eval (finiteHaarModel ι U) i‖ ^ 2 ∂(haarSixProbability ι : Measure _)) ≤
      (t.radius : ℝ) ^ 2 := by
  classical
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he (j : ι) :
      (∫ U, ‖t.eval (finiteHaarModel ι U) j‖ ^ 2 ∂(haarSixProbability ι : Measure _)) =
      (∫ U, ‖t.eval (finiteHaarModel ι U) i‖ ^ 2 ∂(haarSixProbability ι : Measure _)) :=
    ((finiteExpression_coordinate_identDistrib ι t j i).comp (measurable_norm.pow_const 2)).integral_eq
  calc
    _ = (Fintype.card ι : ℝ)⁻¹ * ∑ j,
        ∫ U, ‖t.eval (finiteHaarModel ι U) j‖ ^ 2 ∂(haarSixProbability ι : Measure _) := by
      simp_rw [he]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
    _ = ∫ U, (Fintype.card ι : ℝ)⁻¹ * ∑ j, ‖t.eval (finiteHaarModel ι U) j‖ ^ 2
        ∂(haarSixProbability ι : Measure _) := by
      rw [integral_const_mul, integral_finsetSum _ (fun j _ =>
        finiteExpression_coordinate_norm_pow_integrable ι t j 2)]
    _ = ∫ U, ‖t.eval (finiteHaarModel ι U)‖ ^ 2 ∂(haarSixProbability ι : Measure _) := by
      simp_rw [← finiteL2_norm_sq ι ℂ]
    _ ≤ ∫ _U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι), (t.radius : ℝ) ^ 2 ∂(haarSixProbability ι : Measure _) := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun U => sq_nonneg _) (integrable_const _)
      exact Filter.Eventually.of_forall fun U =>
        pow_le_pow_left₀ (norm_nonneg _) (t.eval_norm_le (finiteHaarModel ι U)) 2
    _ = _ := by simp

/-- The first-moment bound used to center the concentration estimate. -/
theorem finiteExpression_coordinate_firstMoment_le (t : StabilityExpression) (i : ι) :
    (∫ U, ‖t.eval (finiteHaarModel ι U) i‖ ∂(haarSixProbability ι : Measure _)) ≤ t.radius := by
  have hm : MemLp (fun U => ‖t.eval (finiteHaarModel ι U) i‖) 2
      (haarSixProbability ι : Measure _) :=
    (memLp_two_iff_integrable_sq
      (finiteExpression_coordinate_continuous ι t i).norm.measurable.aestronglyMeasurable).mpr
      (finiteExpression_coordinate_norm_pow_integrable ι t i 2)
  have hv := variance_nonneg (fun U => ‖t.eval (finiteHaarModel ι U) i‖)
    (haarSixProbability ι : Measure _)
  rw [variance_eq_sub hm] at hv
  simp only [Pi.pow_apply] at hv
  have hb := finiteExpression_coordinate_secondMoment_le ι t i
  apply (sq_le_sq₀ (integral_nonneg (fun U => norm_nonneg _)) (NNReal.coe_nonneg _)).mp
  linarith

end OperatorPhaseRetrieval

end
