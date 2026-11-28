module

public import OperatorPhaseRetrieval.GaussianProducts

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace OperatorPhaseRetrieval

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stdGaussian_dual_secondMoment (L : StrongDual ℝ E) :
    ∫ x, L x ^ 2 ∂stdGaussian E = ‖L‖ ^ 2 := by
  have h := variance_dual_stdGaussian L
  rw [variance_eq_integral L.continuous.aemeasurable, integral_strongDual_stdGaussian] at h
  simpa only [sub_zero] using h

/-- The expected squared norm of a standard Gaussian is its real dimension. -/
theorem stdGaussian_norm_secondMoment :
    ∫ x, ‖x‖ ^ 2 ∂stdGaussian E = Module.finrank ℝ E := by
  let b := stdOrthonormalBasis ℝ E
  have hi (i : Fin (Module.finrank ℝ E)) :
      Integrable (fun x : E => (inner ℝ (b i) x) ^ 2) (stdGaussian E) :=
    ((IsGaussian.memLp_two_id (μ := stdGaussian E)).const_inner (b i)).integrable_sq
  have hp (x : E) : ‖x‖ ^ 2 = ∑ i, (inner ℝ (b i) x) ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using (b.sum_sq_norm_inner_right x).symm
  simp_rw [hp]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  have hm (i : Fin (Module.finrank ℝ E)) :
      ∫ x : E, (inner ℝ (b i) x) ^ 2 ∂stdGaussian E = 1 := by
    simpa only [innerSL_apply_apply, innerSL_apply_norm, b.norm_eq_one, one_pow] using
      stdGaussian_dual_secondMoment (innerSL ℝ (b i))
  simp_rw [hm]
  simp

end OperatorPhaseRetrieval

end
