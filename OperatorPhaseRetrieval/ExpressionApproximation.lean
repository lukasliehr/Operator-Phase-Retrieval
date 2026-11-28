module

public import OperatorPhaseRetrieval.TransformedExpressions

@[expose] public section

noncomputable section

open MeasureTheory
open scoped NNReal

namespace OperatorPhaseRetrieval

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- A uniform scalar approximation gives the same L² error on a probability space. -/
theorem compLp_uniform_error_le (ψ φ : ℂ → ℂ) (hψ : LipschitzWith 1 ψ)
    (hφ : LipschitzWith 1 φ) (hψ0 : ψ 0 = 0) (hφ0 : φ 0 = 0)
    (ε : ℝ) (hε : 0 ≤ ε) (he : ∀ z, ‖ψ z - φ z‖ ≤ ε) (f : L2 μ) :
    ‖hψ.compLp hψ0 f - hφ.compLp hφ0 f‖ ≤ ε := by
  have h := Lp.norm_le_of_ae_bound (f := hψ.compLp hψ0 f - hφ.compLp hφ0 f) hε ?_
  · simpa [measureUnivNNReal, measure_univ] using h
  · filter_upwards [Lp.coeFn_sub (hψ.compLp hψ0 f) (hφ.compLp hφ0 f),
      hψ.coeFn_compLp hψ0 f, hφ.coeFn_compLp hφ0 f] with x hsub hx hy
    rw [hsub]
    simp only [Pi.sub_apply, hx, hy, Function.comp_apply]
    exact he (f x)

namespace StabilityExpression

/-- A syntax-dependent bound for the accumulated uniform modulus approximation error. -/
def approximationWeight : StabilityExpression → ℝ≥0
  | .one | .seed => 0
  | .add s t => s.approximationWeight + t.approximationWeight
  | .smul a b t => ‖rationalComplex a b‖₊ * t.approximationWeight
  | .conj t | .apply _ _ t => t.approximationWeight
  | .modulus t => t.approximationWeight + 1

theorem transformedEval_error_le (ψ : ℂ → ℂ) (hψ : LipschitzWith 1 ψ) (hzero : ψ 0 = 0)
    (ε : ℝ) (hε : 0 ≤ ε) (he : ∀ z, ‖ψ z - (‖z‖ : ℂ)‖ ≤ ε)
    (U : Fin 6 → L2 μ ≃ₗᵢ[ℂ] L2 μ) (t : StabilityExpression) :
    ‖transformedEval ψ hψ hzero U t - t.eval U‖ ≤ t.approximationWeight * ε := by
  induction t with
  | one => simp [transformedEval, eval, approximationWeight]
  | seed => simp [transformedEval, eval, approximationWeight]
  | add s t hs ht =>
    simp only [transformedEval, eval, approximationWeight, NNReal.coe_add]
    calc
      _ = ‖(transformedEval ψ hψ hzero U s - s.eval U) +
          (transformedEval ψ hψ hzero U t - t.eval U)‖ := by congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (by simpa [add_mul] using add_le_add hs ht)
  | smul a b t ht =>
    simp only [transformedEval, eval, approximationWeight, ← smul_sub, norm_smul,
      NNReal.coe_mul, coe_nnnorm]
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left ht (norm_nonneg (rationalComplex a b))
  | conj t ht => exact (conjugateL2_sub_le _ _).trans ht
  | modulus t ht =>
    change ‖hψ.compLp hzero (transformedEval ψ hψ hzero U t) - complexModulusL2 (t.eval U)‖ ≤ _
    calc
      _ ≤ ‖hψ.compLp hzero (transformedEval ψ hψ hzero U t) - hψ.compLp hzero (t.eval U)‖ +
          ‖hψ.compLp hzero (t.eval U) - complexModulusL2 (t.eval U)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖transformedEval ψ hψ hzero U t - t.eval U‖ + ε := by
        apply add_le_add
        · simpa only [NNReal.coe_one, one_mul] using hψ.norm_compLp_sub_le hzero _ _
        · exact compLp_uniform_error_le ψ _ hψ lipschitz_complex_modulus hzero (by simp)
            ε hε he (t.eval U)
      _ ≤ _ := by simp only [approximationWeight, NNReal.coe_add, NNReal.coe_one]; nlinarith
  | apply j inverse t ht =>
    simpa only [transformedEval, eval, approximationWeight, ← map_sub,
      (unitaryAction U j inverse).norm_map] using ht

/-- The modulus approximations converge in L² uniformly over the unitary family. -/
theorem smooth_transformedEval_error_le (ε : ℝ) (hε : 0 ≤ ε)
    (U : Fin 6 → L2 μ ≃ₗᵢ[ℂ] L2 μ) (t : StabilityExpression) :
    ‖transformedEval (smoothModulus ε) (smoothModulus_lipschitz ε) (smoothModulus_zero hε) U t - t.eval U‖ ≤
      t.approximationWeight * ε :=
  transformedEval_error_le _ _ _ ε hε (smoothModulus_error_le hε) U t

end StabilityExpression
end OperatorPhaseRetrieval

end
