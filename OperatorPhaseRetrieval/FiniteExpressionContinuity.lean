import OperatorPhaseRetrieval.FiniteHaarModels

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace OperatorPhaseRetrieval

variable (ι : Type*) [Fintype ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem finiteL2Unitary_continuous_apply :
    Continuous (fun p : HaarUnitary (EuclideanSpace ℂ ι) × L2 (finiteProbability ι) =>
      finiteL2Unitary ι p.1 p.2) := by
  change Continuous (fun p : HaarUnitary (EuclideanSpace ℂ ι) × L2 (finiteProbability ι) =>
    finiteL2Equiv ι ℂ ((p.1 : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
      ((finiteL2Equiv ι ℂ).symm p.2)))
  exact (finiteL2Equiv ι ℂ).continuous.comp
    ((continuous_subtype_val.comp continuous_fst).clm_apply
      ((finiteL2Equiv ι ℂ).symm.continuous.comp continuous_snd))

theorem finiteL2Unitary_inverse (U : HaarUnitary (EuclideanSpace ℂ ι)) :
    finiteL2Unitary ι U⁻¹ = (finiteL2Unitary ι U).symm := by
  unfold finiteL2Unitary
  rw [map_inv]
  rfl

theorem finiteL2Unitary_inverse_continuous_apply :
    Continuous (fun p : HaarUnitary (EuclideanSpace ℂ ι) × L2 (finiteProbability ι) =>
      (finiteL2Unitary ι p.1).symm p.2) := by
  have he : (fun p : HaarUnitary (EuclideanSpace ℂ ι) × L2 (finiteProbability ι) =>
      (finiteL2Unitary ι p.1).symm p.2) = fun p => finiteL2Unitary ι p.1⁻¹ p.2 := by
    funext p
    rw [finiteL2Unitary_inverse]
  rw [he]
  have hp : Continuous (fun p : HaarUnitary (EuclideanSpace ℂ ι) × L2 (finiteProbability ι) =>
      (p.1⁻¹, p.2)) := continuous_fst.inv.prodMk continuous_snd
  have hc := (finiteL2Unitary_continuous_apply ι).comp hp
  exact hc

theorem finiteL2_coordinate_continuous (i : ι) :
    Continuous (fun f : L2 (finiteProbability ι) => f i) := by
  have he : (fun f : L2 (finiteProbability ι) => f i) =
      fun f => Real.sqrt (Fintype.card ι) • ((finiteL2Equiv ι ℂ).symm f) i := by
    funext f
    simpa only [(finiteL2Equiv ι ℂ).apply_symm_apply] using
      finiteL2Equiv_apply ι ℂ ((finiteL2Equiv ι ℂ).symm f) i
  rw [he]
  exact ((PiLp.continuous_apply 2 (fun _ : ι => ℂ) i).comp
    (finiteL2Equiv ι ℂ).symm.continuous).const_smul (Real.sqrt (Fintype.card ι))

theorem finiteExpression_continuous (t : StabilityExpression) :
    Continuous (fun U => t.eval (finiteHaarModel ι U)) := by
  have hconj : Continuous (conjugateL2 : L2 (finiteProbability ι) → L2 (finiteProbability ι)) :=
    (LipschitzWith.of_dist_le_mul (K := 1) (fun f g => by
      simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using conjugateL2_sub_le f g)).continuous
  have hmod : Continuous (complexModulusL2 : L2 (finiteProbability ι) → L2 (finiteProbability ι)) :=
    (LipschitzWith.of_dist_le_mul (K := 1) (fun f g => by
      simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using complexModulusL2_sub_le f g)).continuous
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
        finiteL2Unitary ι (U j.succ) (t.eval (finiteHaarModel ι U)))
      have hp : Continuous (fun U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι) =>
          (U j.succ, t.eval (finiteHaarModel ι U))) := (continuous_apply j.succ).prodMk ht
      have hc := (finiteL2Unitary_continuous_apply ι).comp hp
      exact hc
    | true =>
      change Continuous (fun U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι) =>
        (finiteL2Unitary ι (U j.succ)).symm (t.eval (finiteHaarModel ι U)))
      have hp : Continuous (fun U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι) =>
          (U j.succ, t.eval (finiteHaarModel ι U))) := (continuous_apply j.succ).prodMk ht
      have hc := (finiteL2Unitary_inverse_continuous_apply ι).comp hp
      exact hc

theorem finiteExpression_coordinate_continuous (t : StabilityExpression) (i : ι) :
    Continuous (fun U => t.eval (finiteHaarModel ι U) i) :=
  (finiteL2_coordinate_continuous ι i).comp (finiteExpression_continuous ι t)

/-- The random fourth moment appearing in Lemma 4.8 and the Markov selection step. -/
def finiteExpressionFourthMoment (t : StabilityExpression)
    (U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖t.eval (finiteHaarModel ι U) i‖ ^ 4

theorem finiteExpressionFourthMoment_continuous (t : StabilityExpression) :
    Continuous (finiteExpressionFourthMoment ι t) :=
  continuous_const.mul (continuous_finsetSum _ (fun i _ =>
    ((finiteExpression_coordinate_continuous ι t i).norm.pow 4)))

theorem finiteExpressionFourthMoment_integral (t : StabilityExpression)
    (U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) :
    finiteExpressionFourthMoment ι t U =
      ∫ i, ‖t.eval (finiteHaarModel ι U) i‖ ^ 4 ∂finiteProbability ι :=
  (finiteProbability_integral ι _).symm

theorem finiteExpressionFourthMoment_lintegral (t : StabilityExpression)
    (U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) :
    ENNReal.ofReal (finiteExpressionFourthMoment ι t U) =
      ∫⁻ i, ENNReal.ofReal (‖t.eval (finiteHaarModel ι U) i‖ ^ 4) ∂finiteProbability ι := by
  rw [finiteExpressionFourthMoment_integral]
  exact ofReal_integral_eq_lintegral_ofReal (memLp_one_iff_integrable.mp MemLp.of_discrete)
    (Filter.Eventually.of_forall fun i => by positivity)

end OperatorPhaseRetrieval

end
