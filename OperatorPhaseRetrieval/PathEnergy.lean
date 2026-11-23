import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Probability.Moments.Variance

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace OperatorPhaseRetrieval

/-- The elementary energy estimate on a unit interval, used before averaging
unitary paths. The derivative is supplied explicitly. -/
theorem path_squared_difference_le_energy (f d : ℝ → ℝ) (hd : Continuous d)
    (hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (d t) t) :
    (f 1 - f 0) ^ 2 ≤ ∫ t in (0 : ℝ)..1, (d t) ^ 2 := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 1)
  have hprob : IsProbabilityMeasure μ := by
    constructor
    simp [μ]
  let := hprob
  have h2 : MemLp d 2 μ := by
    apply (memLp_two_iff_integrable_sq hd.aestronglyMeasurable).mpr
    exact ((hd.pow 2).continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hv := variance_nonneg d μ
  rw [variance_eq_sub h2] at hv
  have hf : (∫ t in (0 : ℝ)..1, d t) = f 1 - f 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hderiv)
      (hd.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hf ⊢
  change (∫ t, d t ∂μ) = _ at hf
  simp only [Pi.pow_apply] at hv
  rw [hf] at hv
  linarith

end OperatorPhaseRetrieval

end
