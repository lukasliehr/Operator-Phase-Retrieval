module

public import OperatorPhaseRetrieval.ExpressionModels
public import OperatorPhaseRetrieval.LimitStability

@[expose] public section

/-!
# The limit construction from evaluated models

This file assembles the deterministic and compactness portions of the limit construction for Theorem B.
Uniform finite-model stability, fourth moments, and a convergent atomless
marginal are explicit quantitative hypotheses. Their existence is the
probabilistic part of Theorem B.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace OperatorPhaseRetrieval

theorem coordinate_secondMoment_le_of_fourthMoment (ν : ProbabilityMeasure (ℕ → ℂ))
    (r : ℕ) (M : ℝ≥0)
    (hM : ∫⁻ z, ENNReal.ofReal (‖z r‖ ^ 4) ∂(ν : Measure (ℕ → ℂ)) ≤ M) :
    ∫⁻ z, ENNReal.ofReal (‖z r‖ ^ 2) ∂(ν : Measure (ℕ → ℂ)) ≤ (1 + M : ℝ≥0) := by
  calc
    _ ≤ ∫⁻ z, (1 + ENNReal.ofReal (‖z r‖ ^ 4)) ∂(ν : Measure (ℕ → ℂ)) := by
      apply lintegral_mono
      intro z
      have h : ‖z r‖ ^ 2 ≤ 1 + ‖z r‖ ^ 4 := by nlinarith [sq_nonneg (‖z r‖ ^ 2 - 1)]
      simpa only [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ ‖z r‖ ^ 4), ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal h
    _ = 1 + ∫⁻ z, ENNReal.ofReal (‖z r‖ ^ 4) ∂(ν : Measure (ℕ → ℂ)) := by
      rw [lintegral_add_left measurable_const]
      simp
    _ ≤ (1 + M : ℝ≥0) := by
      rw [ENNReal.coe_add, ENNReal.coe_one]
      exact add_le_add le_rfl hM

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    (U : ∀ n, Fin 6 → L2 (μ n) ≃ₗᵢ[ℂ] L2 (μ n))

/-- Actual evaluated models with uniform fourth moments and stability have a
subsequential joint limit with five stable surjective unitaries. The joint laws,
their algebraic and inverse identities, and coordinate density are constructed. -/
theorem exists_stable_expression_limit
    (M : StabilityExpression → ℝ≥0)
    (hM : ∀ n t, ∫⁻ x, ENNReal.ofReal (‖StabilityExpression.eval (U n) t x‖ ^ 4) ∂(μ n) ≤ M t)
    (hStable : ∀ n, StableUnitaryFamily stabilityConstant (fun j : Fin 5 => U n j.succ)) :
    ∃ Q : ProbabilityMeasure (ℕ → ℂ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => StabilityExpression.jointLaw (μ (φ n)) (U (φ n))) atTop (𝓝 Q) ∧
      FiveUnitaryStability (Q : Measure (ℕ → ℂ)) := by
  let P (n : ℕ) := StabilityExpression.jointLaw (μ n) (U n)
  let B (r : ℕ) := M (StabilityExpression.ofIndex r)
  have hB (n r : ℕ) : ∫⁻ z, ENNReal.ofReal (‖z r‖ ^ 4) ∂(P n : Measure (ℕ → ℂ)) ≤ B r := by
    rw [StabilityExpression.jointLaw_fourthMoment]
    exact hM n _
  have hB2 (n r : ℕ) : ∫⁻ z, ENNReal.ofReal (‖z r‖ ^ 2) ∂(P n : Measure (ℕ → ℂ)) ≤ (1 + B r : ℝ≥0) :=
    coordinate_secondMoment_le_of_fourthMoment (P n) r (B r) (hB n r)
  obtain ⟨Q, φ, hφ, hlim⟩ := exists_jointLaw_limit P (fun r => 1 + B r) hB2
  have hQ (r : ℕ) : MemLp (fun z : ℕ → ℂ => z r) 2 (Q : Measure (ℕ → ℂ)) :=
    jointLaw_limit_coordinate_memLp hlim r (1 + B r) (fun n => hB2 (φ n) r)
  refine ⟨Q, φ, hφ, hlim, ?_⟩
  apply fiveUnitaryStability_of_expression_models hlim
    (fun n => StabilityExpression.jointLaw_memLp (μ (φ n)) (U (φ n))) hQ B
    (fun n r => hB (φ n) r)
    StabilityExpression.forwardIndex StabilityExpression.inverseIndex
    StabilityExpression.coordinateOperations
    (fun n => StabilityExpression.jointLaw_algebraLaws (μ (φ n)) (U (φ n)))
  · exact fun n => StabilityExpression.jointLaw_gram (μ (φ n)) (U (φ n))
  · exact fun n => StabilityExpression.jointLaw_inverse (μ (φ n)) (U (φ n))
  · exact fun n => StabilityExpression.jointLaw_stable (μ (φ n)) (U (φ n)) (hStable (φ n))

/-- The final spatial transfer to `L²(ℝ)` from finite model bounds and a convergent
atomless marginal. No limiting space or limiting operators are assumed. The
existence of models satisfying the displayed hypotheses is proved in
`FiveUnitaryStability.lean`. -/
theorem fiveUnitaryStability_real_of_expression_models
    (M : StabilityExpression → ℝ≥0)
    (hM : ∀ n t, ∫⁻ x, ENNReal.ofReal (‖StabilityExpression.eval (U n) t x‖ ^ 4) ∂(μ n) ≤ M t)
    (hStable : ∀ n, StableUnitaryFamily stabilityConstant (fun j : Fin 5 => U n j.succ))
    (r : ℕ) (γ : ProbabilityMeasure ℂ) [NullSingletonClass (γ : Measure ℂ)]
    (hγ : Tendsto (fun n => (StabilityExpression.jointLaw (μ n) (U n)).map
      (fun z => z r)) atTop (𝓝 γ)) :
    FiveUnitaryStability (volume : Measure ℝ) := by
  obtain ⟨Q, φ, hφ, hlim, hQ⟩ := exists_stable_expression_limit μ U M hM hStable
  have hmap := jointLaw_limit_marginal hlim r γ (hγ.comp hφ.tendsto_atTop)
  have he : (Q : Measure (ℕ → ℂ)).map (fun z => z r) = (γ : Measure ℂ) :=
    congrArg (fun ν : ProbabilityMeasure ℂ => (ν : Measure ℂ)) hmap
  let : NullSingletonClass ((Q : Measure (ℕ → ℂ)).map (fun z => z r)) := by
    rw [he]
    infer_instance
  let : NullSingletonClass (Q : Measure (ℕ → ℂ)) :=
    nullSingletonClass_of_map (fun z => z r) (measurable_pi_apply r).aemeasurable
  exact fiveUnitaryStability_transfer hQ

end OperatorPhaseRetrieval

end
