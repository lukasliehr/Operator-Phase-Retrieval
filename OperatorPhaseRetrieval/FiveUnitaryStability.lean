module

public import OperatorPhaseRetrieval.HaarExpressionFourthMoments
public import OperatorPhaseRetrieval.HaarModelSelection
public import OperatorPhaseRetrieval.Completion

@[expose] public section

/-!
# Five unitary measurements with uniform stability

The fourth-moment estimate below is proved on the actual Haar probability spaces.
Combining it with the finite-model selection and limit construction
discharges every hypothesis of the five-unitary stability theorem on `L²(ℝ)`.
-/

noncomputable section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace OperatorPhaseRetrieval

/-- The explicit dimension-independent moment bound obtained from Poincaré. -/
def haarExpressionPoincareBound (t : StabilityExpression) : ℝ≥0 :=
  8 * t.radius ^ 4 + 2304 * t.lipBound ^ 4

/-- The fourth-moment bound for the Haar expression models, without a concentration hypothesis. -/
theorem haarExpressionMomentBounds : HaarExpressionMomentBounds haarExpressionPoincareBound := by
  intro n t
  let ι := Fin (n+1)
  have hi : Integrable (finiteExpressionFourthMoment ι t) (haarSixProbability ι : Measure _) :=
    (finiteExpressionFourthMoment_continuous ι t).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hb : (∫ U, finiteExpressionFourthMoment ι t U ∂(haarSixProbability ι : Measure _)) ≤
      8 * (t.radius : ℝ) ^ 4 + 2304 * (t.lipBound : ℝ) ^ 4 := by
    unfold finiteExpressionFourthMoment
    rw [integral_const_mul, integral_finsetSum _ (fun i _ =>
      finiteExpression_coordinate_norm_pow_integrable ι t i 4)]
    calc
      _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι,
          (8 * (t.radius : ℝ) ^ 4 + 2304 * (t.lipBound : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun i _ => finiteExpression_coordinate_fourthMoment_le ι t i))
          (by positivity)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α := ι)), one_mul]
  calc
    _ = ENNReal.ofReal (∫ U, finiteExpressionFourthMoment ι t U ∂(haarSixProbability ι : Measure _)) := by
      symm
      apply ofReal_integral_eq_lintegral_ofReal hi
      exact Filter.Eventually.of_forall fun U => by unfold finiteExpressionFourthMoment; positivity
    _ ≤ ENNReal.ofReal (8 * (t.radius : ℝ) ^ 4 + 2304 * (t.lipBound : ℝ) ^ 4) :=
      ENNReal.ofReal_le_ofReal hb
    _ = (haarExpressionPoincareBound t : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      congr 1

/-- The selection of finite models, with all Haar-model hypotheses discharged. -/
theorem exists_finiteHaar_models :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      ∃ U : ∀ k, Fin 6 → HaarUnitary (EuclideanSpace ℂ (Fin (n k + 1))),
        (∀ k, StableUnitaryFamily stabilityConstant
          (fun j : Fin 5 => finiteHaarModel (Fin (n k + 1)) (U k) j.succ)) ∧
        (∀ k t, ∫⁻ i, ENNReal.ofReal
          (‖t.eval (finiteHaarModel (Fin (n k + 1)) (U k)) i‖ ^ 4)
          ∂finiteProbability (Fin (n k + 1)) ≤ momentThreshold t.index (haarExpressionPoincareBound t)) ∧
        Tendsto (fun k => finiteHaarLaw (Fin (n k + 1)) (U k)) atTop (𝓝 circularGaussian) :=
  exists_finiteHaar_models_of_moment_bounds haarExpressionPoincareBound haarExpressionMomentBounds

/-- Theorem B on `L²(ℝ)`: five surjective complex unitaries, the first identity,
with lower stability constant `2⁻¹⁰⁰` and upper constant `1`. -/
theorem fiveUnitaryStability_real : FiveUnitaryStability (volume : Measure ℝ) :=
  fiveUnitaryStability_real_of_haar_moment_bounds haarExpressionPoincareBound
    haarExpressionMomentBounds

/-- Theorem B on atomless standard Borel spaces. -/
theorem fiveUnitaryStability_standardBorel {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] (μ : Measure X) [SigmaFinite μ] [NeZero μ] [NullSingletonClass μ] :
    FiveUnitaryStability μ :=
  fiveUnitaryStability_transfer (μ := (volume : Measure ℝ)) (ν := μ) fiveUnitaryStability_real

/-- The same stability constants hold on the completion of the measure space. -/
theorem fiveUnitaryStability_completion {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] (μ : Measure X) [SigmaFinite μ] [NeZero μ] [NullSingletonClass μ] :
    FiveUnitaryStability μ.completion := by
  obtain ⟨U, _, hU⟩ := fiveUnitaryStability_standardBorel μ
  exact fiveUnitaryStability_of_family (transportUnitaryFamily (completionL2Equiv μ) U)
    (stableUnitaryFamily_transport (completionL2Equiv μ) (completionL2Equiv_modEq μ)
      (fun f g => (hU f g).1))

end OperatorPhaseRetrieval

end
