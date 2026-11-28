module

public import OperatorPhaseRetrieval.SmoothModulus

@[expose] public section

noncomputable section

open MeasureTheory
open scoped NNReal

namespace OperatorPhaseRetrieval
namespace StabilityExpression

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  (ψ : ℂ → ℂ) (hψ : LipschitzWith 1 ψ) (hzero : ψ 0 = 0)

def transformedEval (U : Fin 6 → L2 μ ≃ₗᵢ[ℂ] L2 μ) : StabilityExpression → L2 μ
  | .one => Lp.const 2 μ 1
  | .seed => U 0 (Lp.const 2 μ 1)
  | .add s t => transformedEval U s + transformedEval U t
  | .smul a b t => rationalComplex a b • transformedEval U t
  | .conj t => conjugateL2 (transformedEval U t)
  | .modulus t => hψ.compLp hzero (transformedEval U t)
  | .apply j inverse t => unitaryAction U j inverse (transformedEval U t)

theorem transformedEval_norm_le (U : Fin 6 → L2 μ ≃ₗᵢ[ℂ] L2 μ) (t : StabilityExpression) :
    ‖transformedEval ψ hψ hzero U t‖ ≤ t.radius := by
  induction t with
  | one => simp [transformedEval, radius, Lp.norm_const]
  | seed => simp [transformedEval, radius, Lp.norm_const]
  | add s t hs ht =>
    exact (norm_add_le _ _).trans (by simpa [radius] using add_le_add hs ht)
  | smul a b t ht =>
    simpa [transformedEval, radius, norm_smul] using
      mul_le_mul_of_nonneg_left ht (norm_nonneg (rationalComplex a b))
  | conj t ht => exact (conjugateL2_norm_le _).trans ht
  | modulus t ht =>
    exact (hψ.norm_compLp_le hzero _).trans (by simpa only [NNReal.coe_one, one_mul, radius] using ht)
  | apply j inverse t ht => simpa [transformedEval, radius] using ht

theorem transformedEval_sub_le (U V : Fin 6 → L2 μ ≃ₗᵢ[ℂ] L2 μ) (t : StabilityExpression) :
    ‖transformedEval ψ hψ hzero U t - transformedEval ψ hψ hzero V t‖ ≤
      t.lipBound * unitaryFamilyDistance U V := by
  induction t with
  | one => simp [transformedEval, lipBound]
  | seed => simpa [transformedEval, lipBound, Lp.norm_const] using
      unitaryFamily_apply_sub_le U V 0 (Lp.const 2 μ 1)
  | add s t hs ht =>
    simp only [transformedEval, lipBound, NNReal.coe_add]
    calc
      _ = ‖(transformedEval ψ hψ hzero U s - transformedEval ψ hψ hzero V s) +
          (transformedEval ψ hψ hzero U t - transformedEval ψ hψ hzero V t)‖ := by congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (by simpa [add_mul] using add_le_add hs ht)
  | smul a b t ht =>
    simp only [transformedEval, lipBound, ← smul_sub, norm_smul, NNReal.coe_mul, coe_nnnorm]
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left ht (norm_nonneg (rationalComplex a b))
  | conj t ht => exact (conjugateL2_sub_le _ _).trans ht
  | modulus t ht =>
    apply (hψ.norm_compLp_sub_le hzero _ _).trans
    simpa only [NNReal.coe_one, one_mul, lipBound] using ht
  | apply j inverse t ht =>
    exact (unitaryAction_sub_le U V j inverse _ _).trans (by
      have hb := mul_le_mul_of_nonneg_left (transformedEval_norm_le ψ hψ hzero V t)
        (unitaryFamilyDistance_nonneg U V)
      change _ ≤ ((t.lipBound : ℝ) + t.radius) * unitaryFamilyDistance U V
      nlinarith)

end StabilityExpression
end OperatorPhaseRetrieval

end
