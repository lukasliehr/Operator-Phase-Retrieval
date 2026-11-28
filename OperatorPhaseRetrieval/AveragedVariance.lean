module

public import OperatorPhaseRetrieval.MathlibImports
public import Mathlib.Probability.Moments.Variance

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace OperatorPhaseRetrieval

/-- Pairwise squared differences have mean twice the variance. -/
theorem integral_integral_sq_sub_eq_two_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℝ) (hF : MemLp F 2 μ) :
    (∫ x, ∫ y, (F y - F x) ^ 2 ∂μ ∂μ) = 2 * variance F μ := by
  have hi : Integrable F μ := hF.integrable (by norm_num)
  have h2 : Integrable (fun x => F x ^ 2) μ := (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).mp hF
  let m := ∫ x, F x ∂μ
  let q := ∫ x, F x ^ 2 ∂μ
  have he (x : Ω) : (∫ y, (F y - F x) ^ 2 ∂μ) = q - (2*m) * F x + F x ^ 2 := by
    have hp (y : Ω) : (F y - F x) ^ 2 = F y ^ 2 - (2*F x) * F y + F x ^ 2 := by ring
    simp_rw [hp]
    rw [integral_add (f := fun y => F y ^ 2 - (2*F x) * F y)
      (h2.sub (hi.const_mul _)) (integrable_const _),
      integral_sub h2 (hi.const_mul (2 * F x)), integral_const_mul]
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    dsimp [q, m]
    ring
  simp_rw [he]
  rw [integral_add (f := fun x => q - (2*m) * F x)
      ((integrable_const _).sub (hi.const_mul _)) h2,
    integral_sub (integrable_const q) (hi.const_mul (2*m)), integral_const_mul,
    variance_eq_sub hF]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, Pi.pow_apply]
  dsimp [q, m]
  ring

end OperatorPhaseRetrieval

end
