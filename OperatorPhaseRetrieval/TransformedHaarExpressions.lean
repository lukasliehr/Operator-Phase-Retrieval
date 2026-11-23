import OperatorPhaseRetrieval.HaarExchangeability
import OperatorPhaseRetrieval.TransformedExpressions

noncomputable section

open MeasureTheory ProbabilityTheory

namespace OperatorPhaseRetrieval

variable (ι : Type*) [Fintype ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (ψ : ℂ → ℂ) (hψ : LipschitzWith 1 ψ) (hzero : ψ 0 = 0)

theorem finiteL2Unitary_permutation_compLp (p : Equiv.Perm ι) (f : L2 (finiteProbability ι)) :
    finiteL2Unitary ι (permutationHaarUnitary ι p) (hψ.compLp hzero f) =
      hψ.compLp hzero (finiteL2Unitary ι (permutationHaarUnitary ι p) f) := by
  have h₁ := (finiteProbability_ae_iff ι).mp (hψ.coeFn_compLp hzero f)
  have h₂ := (finiteProbability_ae_iff ι).mp
    (hψ.coeFn_compLp hzero (finiteL2Unitary ι (permutationHaarUnitary ι p) f))
  apply Lp.ext
  exact Filter.Eventually.of_forall fun i => by
    simp only [finiteL2Unitary_permutation_apply, h₁, h₂, Function.comp_apply]

theorem finiteTransformedExpression_continuous (t : StabilityExpression) :
    Continuous (fun U => StabilityExpression.transformedEval ψ hψ hzero (finiteHaarModel ι U) t) := by
  have hconj : Continuous (conjugateL2 : L2 (finiteProbability ι) → L2 (finiteProbability ι)) :=
    (LipschitzWith.of_dist_le_mul (K := 1) (fun f g => by
      simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using conjugateL2_sub_le f g)).continuous
  have hmod : Continuous (fun f : L2 (finiteProbability ι) => hψ.compLp hzero f) :=
    (LipschitzWith.of_dist_le_mul (K := 1) (fun f g => by
      simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using hψ.norm_compLp_sub_le hzero f g)).continuous
  induction t with
  | one => exact continuous_const
  | seed =>
    change Continuous (fun U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι) =>
      finiteL2Unitary ι (U 0) (Lp.const 2 (finiteProbability ι) 1))
    have hp : Continuous (fun U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι) =>
        (U 0, Lp.const 2 (finiteProbability ι) (1 : ℂ))) :=
      (continuous_apply 0).prodMk continuous_const
    have hc := (finiteL2Unitary_continuous_apply ι).comp hp
    exact hc
  | add s t hs ht => exact hs.add ht
  | smul a b t ht => exact ht.const_smul (rationalComplex a b)
  | conj t ht => exact hconj.comp ht
  | modulus t ht => exact hmod.comp ht
  | apply j inverse t ht =>
    cases inverse with
    | false =>
      change Continuous (fun U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι) =>
        finiteL2Unitary ι (U j.succ) (StabilityExpression.transformedEval ψ hψ hzero (finiteHaarModel ι U) t))
      have hp : Continuous (fun U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι) =>
          (U j.succ, StabilityExpression.transformedEval ψ hψ hzero (finiteHaarModel ι U) t)) := (continuous_apply j.succ).prodMk ht
      have hc := (finiteL2Unitary_continuous_apply ι).comp hp
      exact hc
    | true =>
      change Continuous (fun U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι) =>
        (finiteL2Unitary ι (U j.succ)).symm (StabilityExpression.transformedEval ψ hψ hzero (finiteHaarModel ι U) t))
      have hp : Continuous (fun U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι) =>
          (U j.succ, StabilityExpression.transformedEval ψ hψ hzero (finiteHaarModel ι U) t)) := (continuous_apply j.succ).prodMk ht
      have hc := (finiteL2Unitary_inverse_continuous_apply ι).comp hp
      exact hc

theorem finiteTransformedExpression_coordinate_continuous (t : StabilityExpression) (i : ι) :
    Continuous (fun U => StabilityExpression.transformedEval ψ hψ hzero (finiteHaarModel ι U) t i) :=
  (finiteL2_coordinate_continuous ι i).comp (finiteTransformedExpression_continuous ι ψ hψ hzero t)

/-- Permutation equivariance holds for every expression, including inverse
operators, conjugation and modulus. -/
theorem finiteTransformedExpression_conjugate_permutation (p : Equiv.Perm ι)
    (U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) (t : StabilityExpression) :
    StabilityExpression.transformedEval ψ hψ hzero (finiteHaarModel ι (haarSixConjugate ι (permutationHaarUnitary ι p) U)) t =
      finiteL2Unitary ι (permutationHaarUnitary ι p) (StabilityExpression.transformedEval ψ hψ hzero (finiteHaarModel ι U) t) := by
  induction t with
  | one => exact (finiteL2Unitary_permutation_one ι p).symm
  | seed =>
    change finiteHaarModel ι (haarSixConjugate ι (permutationHaarUnitary ι p) U) 0
      (Lp.const 2 (finiteProbability ι) 1) = _
    nth_rw 1 [← finiteL2Unitary_permutation_one ι p]
    exact finiteHaarModel_conjugate_apply ι _ U 0 _
  | add s t hs ht => simp only [StabilityExpression.transformedEval, hs, ht, map_add]
  | smul a b t ht => simp only [StabilityExpression.transformedEval, ht, map_smul]
  | conj t ht =>
    simp only [StabilityExpression.transformedEval, ht, finiteL2Unitary_permutation_conj]
  | modulus t ht =>
    simp only [StabilityExpression.transformedEval, ht, finiteL2Unitary_permutation_compLp]
  | apply j inverse t ht =>
    cases inverse with
    | false =>
      simp only [StabilityExpression.transformedEval, unitaryAction, Bool.false_eq_true, ↓reduceIte, ht]
      exact finiteHaarModel_conjugate_apply ι _ U j.succ _
    | true =>
      simp only [StabilityExpression.transformedEval, unitaryAction, ↓reduceIte, ht]
      exact finiteHaarModel_conjugate_inverse_apply ι _ U j.succ _

/-- The coordinate laws of every expression are invariant under permutations. -/
theorem finiteTransformedExpression_coordinate_law_permutation (p : Equiv.Perm ι)
    (t : StabilityExpression) (i : ι) :
    (haarSixProbability ι : Measure _).map (fun U => StabilityExpression.transformedEval ψ hψ hzero (finiteHaarModel ι U) t i) =
    (haarSixProbability ι : Measure _).map (fun U => StabilityExpression.transformedEval ψ hψ hzero (finiteHaarModel ι U) t (p.symm i)) := by
  have hc := haarSixConjugate_measurePreserving ι (permutationHaarUnitary ι p)
  have he := congrArg (fun μ : Measure (Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) =>
    μ.map (fun U => StabilityExpression.transformedEval ψ hψ hzero (finiteHaarModel ι U) t i)) hc.map_eq
  rw [Measure.map_map (finiteTransformedExpression_coordinate_continuous ι ψ hψ hzero t i).measurable hc.measurable] at he
  simpa only [Function.comp_def, finiteTransformedExpression_conjugate_permutation,
    finiteL2Unitary_permutation_apply] using he.symm

/-- In particular, any two coordinates of an expression have the same law. -/
theorem finiteTransformedExpression_coordinate_identDistrib (t : StabilityExpression) (i j : ι) :
    IdentDistrib (fun U => StabilityExpression.transformedEval ψ hψ hzero (finiteHaarModel ι U) t i)
      (fun U => StabilityExpression.transformedEval ψ hψ hzero (finiteHaarModel ι U) t j)
      (haarSixProbability ι : Measure _) (haarSixProbability ι : Measure _) := by
  classical
  refine ⟨(finiteTransformedExpression_coordinate_continuous ι ψ hψ hzero t i).measurable.aemeasurable,
    (finiteTransformedExpression_coordinate_continuous ι ψ hψ hzero t j).measurable.aemeasurable, ?_⟩
  simpa only [Equiv.symm_swap, Equiv.swap_apply_left] using
    finiteTransformedExpression_coordinate_law_permutation ι ψ hψ hzero (Equiv.swap i j) t i

theorem finiteTransformedExpression_coordinate_norm_pow_integrable (t : StabilityExpression) (i : ι) (p : ℕ) :
    Integrable (fun U => ‖StabilityExpression.transformedEval ψ hψ hzero (finiteHaarModel ι U) t i‖ ^ p) (haarSixProbability ι : Measure _) :=
  ((finiteTransformedExpression_coordinate_continuous ι ψ hψ hzero t i).norm.pow p).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Exchangeability turns the deterministic normalized L² bound into a
uniform second-moment bound for every coordinate. -/
theorem finiteTransformedExpression_coordinate_secondMoment_le (t : StabilityExpression) (i : ι) :
    (∫ U, ‖StabilityExpression.transformedEval ψ hψ hzero (finiteHaarModel ι U) t i‖ ^ 2 ∂(haarSixProbability ι : Measure _)) ≤
      (t.radius : ℝ) ^ 2 := by
  classical
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he (j : ι) :
      (∫ U, ‖StabilityExpression.transformedEval ψ hψ hzero (finiteHaarModel ι U) t j‖ ^ 2 ∂(haarSixProbability ι : Measure _)) =
      (∫ U, ‖StabilityExpression.transformedEval ψ hψ hzero (finiteHaarModel ι U) t i‖ ^ 2 ∂(haarSixProbability ι : Measure _)) :=
    ((finiteTransformedExpression_coordinate_identDistrib ι ψ hψ hzero t j i).comp (measurable_norm.pow_const 2)).integral_eq
  calc
    _ = (Fintype.card ι : ℝ)⁻¹ * ∑ j,
        ∫ U, ‖StabilityExpression.transformedEval ψ hψ hzero (finiteHaarModel ι U) t j‖ ^ 2 ∂(haarSixProbability ι : Measure _) := by
      simp_rw [he]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
    _ = ∫ U, (Fintype.card ι : ℝ)⁻¹ * ∑ j, ‖StabilityExpression.transformedEval ψ hψ hzero (finiteHaarModel ι U) t j‖ ^ 2
        ∂(haarSixProbability ι : Measure _) := by
      rw [integral_const_mul, integral_finsetSum _ (fun j _ =>
        finiteTransformedExpression_coordinate_norm_pow_integrable ι ψ hψ hzero t j 2)]
    _ = ∫ U, ‖StabilityExpression.transformedEval ψ hψ hzero (finiteHaarModel ι U) t‖ ^ 2 ∂(haarSixProbability ι : Measure _) := by
      simp_rw [← finiteL2_norm_sq ι ℂ]
    _ ≤ ∫ _U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι), (t.radius : ℝ) ^ 2 ∂(haarSixProbability ι : Measure _) := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun U => sq_nonneg _) (integrable_const _)
      exact Filter.Eventually.of_forall fun U =>
        pow_le_pow_left₀ (norm_nonneg _) (StabilityExpression.transformedEval_norm_le ψ hψ hzero (finiteHaarModel ι U) t) 2
    _ = _ := by simp


end OperatorPhaseRetrieval

end
