import OperatorPhaseRetrieval.HaarEmpiricalLaw
import OperatorPhaseRetrieval.ExpressionLimit

/-!
# Selection of the actual finite Haar models

The marginal and stability failure estimates are proved in the imported modules.
The dimension-independent expression fourth moments are explicit inputs here.
`FiveUnitaryStability.lean` proves those inputs and derives the unconditional
Theorem 1.3 and finite-model selection.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace OperatorPhaseRetrieval

/-- The quantitative input from Lemma 4.8, for actual Haar matrices. -/
def HaarExpressionMomentBounds (M : StabilityExpression → ℝ≥0) : Prop :=
  ∀ n t, ∫⁻ U, ENNReal.ofReal (finiteExpressionFourthMoment (Fin (n+1)) t U)
    ∂(haarSixProbability (Fin (n+1)) : Measure _) ≤ M t

/-- Selection with stability and the Gaussian marginal already discharged.
The only input is the dimension-independent fourth-moment expectation bound. -/
theorem exists_finiteHaar_models_of_moment_bounds
    (M : StabilityExpression → ℝ≥0) (hM : HaarExpressionMomentBounds M) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      ∃ U : ∀ k, Fin 6 → HaarUnitary (EuclideanSpace ℂ (Fin (n k + 1))),
        (∀ k, StableUnitaryFamily stabilityConstant
          (fun j : Fin 5 => finiteHaarModel (Fin (n k + 1)) (U k) j.succ)) ∧
        (∀ k t, ∫⁻ i, ENNReal.ofReal
          (‖t.eval (finiteHaarModel (Fin (n k + 1)) (U k)) i‖ ^ 4)
          ∂finiteProbability (Fin (n k + 1)) ≤ momentThreshold t.index (M t)) ∧
        Tendsto (fun k => finiteHaarLaw (Fin (n k + 1)) (U k)) atTop (𝓝 circularGaussian) := by
  let Ω (n : ℕ) := Fin 6 → HaarUnitary (EuclideanSpace ℂ (Fin (n+1)))
  let P (n : ℕ) : Measure (Ω n) := haarSixProbability (Fin (n+1))
  let F (n r : ℕ) (U : Ω n) : ℝ≥0∞ :=
    ENNReal.ofReal (finiteExpressionFourthMoment (Fin (n+1)) (StabilityExpression.ofIndex r) U)
  let A (n : ℕ) : Set (Ω n) := {U | ¬ StableUnitaryFamily stabilityConstant
    (fun j : Fin 5 => finiteHaarModel (Fin (n+1)) U j.succ)}
  let B (n k : ℕ) : Set (Ω n) :=
    {U | 1 / ((k : ℝ) + 1) ≤ gaussianMarginalError (finiteHaarLaw (Fin (n+1)) U)}
  have hF (n r : ℕ) : AEMeasurable (F n r) (P n) :=
    ((finiteExpressionFourthMoment_continuous (Fin (n+1)) (StabilityExpression.ofIndex r)).measurable.ennreal_ofReal).aemeasurable
  have hA (n : ℕ) (hn : 50 ≤ n) : P n (A n) ≤ 1 / 4 :=
    finiteHaarModel_stability_failure_quarter (Fin (n+1)) (by simpa using (by omega : 50 ≤ n+1))
  have hB (k : ℕ) : ∃ N, ∀ n, N ≤ n → P n (B n k) ≤ 1 / 8 :=
    finiteHaarLaw_error_probability_eventually _ (by positivity)
  obtain ⟨n, hn, _, U, hU⟩ := select_increasing_models Ω P F hF
    (fun r => M (StabilityExpression.ofIndex r)) (fun n r => hM n (StabilityExpression.ofIndex r))
    A hA B hB
  refine ⟨n, hn, U, ?_, ?_, ?_⟩
  · intro k
    exact not_not.mp (hU k).2.1
  · intro k t
    have h := (hU k).2.2.2 t.index
    simpa only [F, StabilityExpression.ofIndex_index,
      finiteExpressionFourthMoment_lintegral] using h
  · have hb (k : ℕ) : gaussianMarginalError (finiteHaarLaw (Fin (n k + 1)) (U k)) ≤
        1 / ((k : ℝ) + 1) := (lt_of_not_ge (hU k).2.2.1).le
    have hz : Tendsto (fun k => gaussianMarginalError
        (finiteHaarLaw (Fin (n k + 1)) (U k))) atTop (𝓝 0) :=
      squeeze_zero (fun k => gaussianMarginalError_nonneg _) hb
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hw : Tendsto (fun k => LevyProkhorov.probabilityMeasureHomeomorph
        (finiteHaarLaw (Fin (n k + 1)) (U k))) atTop
        (𝓝 (LevyProkhorov.probabilityMeasureHomeomorph circularGaussian)) :=
      tendsto_iff_dist_tendsto_zero.mpr hz
    have hh := LevyProkhorov.probabilityMeasureHomeomorph.symm.continuous.continuousAt.tendsto.comp hw
    simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using hh

/-- The seed coordinate in the joint syntax law is precisely its empirical law. -/
theorem finiteHaarLaw_jointLaw_seed (n : ℕ)
    (U : Fin 6 → HaarUnitary (EuclideanSpace ℂ (Fin (n+1)))) :
    (StabilityExpression.jointLaw (finiteProbability (Fin (n+1)))
      (finiteHaarModel (Fin (n+1)) U)).map
      (measurable_pi_apply StabilityExpression.seed.index).aemeasurable =
      finiteHaarLaw (Fin (n+1)) U := by
  apply Subtype.ext
  change ((finiteProbability (Fin (n+1))).map
    (StabilityExpression.coordinateMap _ _)).map _ =
    (finiteProbability (Fin (n+1))).map (finiteHaarSeed (Fin (n+1)) U)
  rw [Measure.map_map (measurable_pi_apply _) (StabilityExpression.coordinateMap_measurable _ _)]
  congr 1
  funext i
  simp only [Function.comp_def, StabilityExpression.coordinateMap,
    StabilityExpression.ofIndex_index, StabilityExpression.eval, finiteHaarSeed]

/-- All of Theorem 1.3 follows from the uniform expectation
estimate for the actual finite Haar expressions. This theorem retains that
estimate as an explicit hypothesis. -/
theorem fiveUnitaryStability_real_of_haar_moment_bounds
    (M : StabilityExpression → ℝ≥0) (hM : HaarExpressionMomentBounds M) :
    FiveUnitaryStability (volume : Measure ℝ) := by
  obtain ⟨n, _, U, hS, hMom, hG⟩ := exists_finiteHaar_models_of_moment_bounds M hM
  apply fiveUnitaryStability_real_of_expression_models
    (fun k => finiteProbability (Fin (n k + 1)))
    (fun k => finiteHaarModel (Fin (n k + 1)) (U k))
    (fun t => momentThreshold t.index (M t)) hMom hS
    StabilityExpression.seed.index circularGaussian
  simpa only [finiteHaarLaw_jointLaw_seed] using hG

end OperatorPhaseRetrieval

end
