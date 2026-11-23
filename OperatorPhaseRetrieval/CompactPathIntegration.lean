import OperatorPhaseRetrieval.HaarIncrementVariance
import OperatorPhaseRetrieval.PathEnergy

noncomputable section

open MeasureTheory Set

namespace OperatorPhaseRetrieval

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [FirstCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

omit [MeasurableSpace X] [BorelSpace X] in
theorem compact_unitInterval_integral_continuous {f : X → ℝ → ℝ}
    (hf : Continuous (Function.uncurry f)) :
    Continuous (fun x => ∫ t in (0 : ℝ)..1, f x t) := by
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]
  exact continuous_parametric_integral_of_continuous hf isCompact_Icc

omit [FirstCountableTopology X] in
/-- Continuous compact-parameter integrals commute with integration on the unit interval. -/
theorem compact_unitInterval_integral_swap {f : X → ℝ → ℝ}
    (hf : Continuous (Function.uncurry f)) :
    (∫ x, (∫ t in (0 : ℝ)..1, f x t) ∂μ) = ∫ t in (0 : ℝ)..1, ∫ x, f x t ∂μ := by
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]
  apply integral_integral_swap
  have hm : μ.prod (volume.restrict (Icc (0 : ℝ) 1)) =
      (μ.prod volume).restrict (univ ×ˢ Icc (0 : ℝ) 1) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [hm]
  exact hf.continuousOn.integrableOn_compact (isCompact_univ.prod isCompact_Icc)

end OperatorPhaseRetrieval

end
