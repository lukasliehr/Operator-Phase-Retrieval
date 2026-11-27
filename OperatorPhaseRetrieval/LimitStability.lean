import OperatorPhaseRetrieval.CoordinateDensity
import OperatorPhaseRetrieval.UnitaryExtension

/-!
# Constructing the limiting stable unitaries from coordinate models

The operators in this file are constructed, not supplied as hypotheses.
The input is a weakly convergent sequence of coordinate laws, uniform fourth
moments, the finite models' Gram and inverse identities, the algebraic identities of formal
expressions, and the finite stability estimates. The second theorem proves
coordinate density from these identities. Producing the finite models with
the required probabilistic estimates is done in `FiveUnitaryStability.lean`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology InnerProductSpace

namespace OperatorPhaseRetrieval

/-- The operator-construction and stability-passage part of the limit construction.
In particular, the conclusion supplies five surjective complex-linear unitaries
on the actual limiting `L²` space and normalizes the first to the identity. -/
theorem fiveUnitaryStability_of_jointLaw_models
    {P : ℕ → ProbabilityMeasure (ℕ → ℂ)} {Q : ProbabilityMeasure (ℕ → ℂ)}
    (hlim : Tendsto P atTop (𝓝 Q))
    (hP : ∀ n r, MemLp (fun z : ℕ → ℂ => z r) 2 (P n : Measure (ℕ → ℂ)))
    (hQ : ∀ r, MemLp (fun z : ℕ → ℂ => z r) 2 (Q : Measure (ℕ → ℂ)))
    (M : ℕ → ℝ≥0)
    (hM : ∀ n r, ∫⁻ z, ENNReal.ofReal (‖z r‖ ^ 4) ∂(P n : Measure (ℕ → ℂ)) ≤ M r)
    (a b : Fin 5 → ℕ → ℕ)
    (hDense : DenseRange (jointCoordinate Q hQ))
    (hGram : ∀ n j r s,
      ⟪jointCoordinate (P n) (hP n) (a j r), jointCoordinate (P n) (hP n) (a j s)⟫_ℂ =
        ⟪jointCoordinate (P n) (hP n) r, jointCoordinate (P n) (hP n) s⟫_ℂ)
    (hInv : ∀ n j r, ∀ᵐ z ∂(P n : Measure (ℕ → ℂ)), z (a j (b j r)) = z r)
    (hStable : ∀ n r s, stabilityConstant * phaseDistance
      (jointCoordinate (P n) (hP n) r) (jointCoordinate (P n) (hP n) s) ≤
        coordinateMeasurementDistance (P n) (hP n) a r s) :
    FiveUnitaryStability (Q : Measure (ℕ → ℂ)) := by
  have hGramQ (j : Fin 5) (r s : ℕ) :
      ⟪jointCoordinate Q hQ r, jointCoordinate Q hQ s⟫_ℂ =
        ⟪jointCoordinate Q hQ (a j r), jointCoordinate Q hQ (a j s)⟫_ℂ := by
    exact tendsto_nhds_unique
      ((jointCoordinate_inner_tendsto hlim hP hQ M hM r s).congr'
        (Eventually.of_forall fun n => (hGram n j r s).symm))
      (jointCoordinate_inner_tendsto hlim hP hQ M hM (a j r) (a j s))
  have hInvQ (j : Fin 5) (r : ℕ) :
      jointCoordinate Q hQ (a j (b j r)) = jointCoordinate Q hQ r := by
    have h := jointLaw_limit_ae_eq hlim _ _ (continuous_apply (a j (b j r)))
      (continuous_apply r) (fun n => hInv n j r)
    apply Lp.ext
    filter_upwards [h, jointCoordinate_coeFn Q hQ (a j (b j r)),
      jointCoordinate_coeFn Q hQ r] with z hz ha hr
    rw [ha, hr, hz]
  have hspan : Dense (Submodule.span ℂ (Set.range (jointCoordinate Q hQ)) :
      Set (L2 (Q : Measure (ℕ → ℂ)))) := hDense.mono (Submodule.subset_span)
  have hex (j : Fin 5) : ∃ U : L2 (Q : Measure (ℕ → ℂ)) ≃ₗᵢ[ℂ] L2 (Q : Measure (ℕ → ℂ)),
      ∀ r, U (jointCoordinate Q hQ r) = jointCoordinate Q hQ (a j r) := by
    apply exists_unitary_of_gram_of_range_subset _ _ hspan ?_ (hGramQ j)
    rintro _ ⟨r, rfl⟩
    exact ⟨b j r, hInvQ j r⟩
  choose U hU using hex
  apply fiveUnitaryStability_of_family U
  apply stableUnitaryFamily_of_dense U hDense
  rintro _ ⟨r, rfl⟩ _ ⟨s, rfl⟩
  have h := le_of_tendsto_of_tendsto
    (tendsto_const_nhds.mul (jointCoordinate_phaseDistance_tendsto hlim hP hQ M hM r s))
    (coordinateMeasurementDistance_tendsto hlim hP hQ M hM a r s)
    (Eventually.of_forall fun n => hStable n r s)
  simpa only [measurementDistance, hU, coordinateMeasurementDistance] using h

/-- The limiting construction with density proved from the finite formal-expression
identities. The remaining inputs are quantitative finite-model hypotheses. -/
theorem fiveUnitaryStability_of_expression_models
    {P : ℕ → ProbabilityMeasure (ℕ → ℂ)} {Q : ProbabilityMeasure (ℕ → ℂ)}
    (hlim : Tendsto P atTop (𝓝 Q))
    (hP : ∀ n r, MemLp (fun z : ℕ → ℂ => z r) 2 (P n : Measure (ℕ → ℂ)))
    (hQ : ∀ r, MemLp (fun z : ℕ → ℂ => z r) 2 (Q : Measure (ℕ → ℂ)))
    (M : ℕ → ℝ≥0)
    (hM : ∀ n r, ∫⁻ z, ENNReal.ofReal (‖z r‖ ^ 4) ∂(P n : Measure (ℕ → ℂ)) ≤ M r)
    (a b : Fin 5 → ℕ → ℕ)
    (ops : CoordinateOperations)
    (hLaws : ∀ n, CoordinateAlgebraLaws ops (P n : Measure (ℕ → ℂ)))
    (hGram : ∀ n j r s,
      ⟪jointCoordinate (P n) (hP n) (a j r), jointCoordinate (P n) (hP n) (a j s)⟫_ℂ =
        ⟪jointCoordinate (P n) (hP n) r, jointCoordinate (P n) (hP n) s⟫_ℂ)
    (hInv : ∀ n j r, ∀ᵐ z ∂(P n : Measure (ℕ → ℂ)), z (a j (b j r)) = z r)
    (hStable : ∀ n r s, stabilityConstant * phaseDistance
      (jointCoordinate (P n) (hP n) r) (jointCoordinate (P n) (hP n) s) ≤
        coordinateMeasurementDistance (P n) (hP n) a r s) :
    FiveUnitaryStability (Q : Measure (ℕ → ℂ)) :=
  fiveUnitaryStability_of_jointLaw_models hlim hP hQ M hM a b
    ((CoordinateAlgebraLaws.weakLimit ops hlim hLaws).denseRange hQ) hGram hInv hStable

end OperatorPhaseRetrieval

end
