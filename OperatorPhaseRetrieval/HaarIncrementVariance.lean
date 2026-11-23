import OperatorPhaseRetrieval.AveragedVariance
import Mathlib.MeasureTheory.Group.Integral

noncomputable section

open MeasureTheory ProbabilityTheory

namespace OperatorPhaseRetrieval

/-- Integrating a continuous function over a compact probability space is continuous
in a locally compact, first-countable parameter. -/
theorem compact_integral_continuous {X Y : Type*}
    [TopologicalSpace X] [FirstCountableTopology X] [LocallyCompactSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] {f : X → Y → ℝ}
    (hf : Continuous (Function.uncurry f)) : Continuous (fun x => ∫ y, f x y ∂μ) := by
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous (μ := μ) hf isCompact_univ)

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [FirstCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]

/-- Averaging conjugated group increments recovers twice the variance. -/
theorem haar_conjugated_increment_variance (F : G → ℝ) (hF : Continuous F) :
    (∫ W, ∫ U, ∫ Z, (F (U * (Z * W * Z⁻¹)) - F U) ^ 2 ∂μ ∂μ ∂μ) =
      2 * variance F μ := by
  have hc : Continuous (fun p : (G × G) × G =>
      (F (p.1.2 * (p.2 * p.1.1 * p.2⁻¹)) - F p.1.2) ^ 2) := by fun_prop
  have hswap : (∫ W, ∫ U, ∫ Z, (F (U * (Z * W * Z⁻¹)) - F U) ^ 2 ∂μ ∂μ ∂μ) =
      ∫ U, ∫ W, ∫ Z, (F (U * (Z * W * Z⁻¹)) - F U) ^ 2 ∂μ ∂μ ∂μ := by
    apply integral_integral_swap_of_hasCompactSupport
    · exact compact_integral_continuous μ hc
    · exact HasCompactSupport.of_compactSpace _
  rw [hswap]
  have he (U : G) : (∫ W, ∫ Z, (F (U * (Z * W * Z⁻¹)) - F U) ^ 2 ∂μ ∂μ) =
      ∫ y, (F y - F U) ^ 2 ∂μ := by
    rw [integral_integral_swap_of_hasCompactSupport
      (show Continuous (fun p : G × G => (F (U * (p.2 * p.1 * p.2⁻¹)) - F U) ^ 2) by fun_prop)
      (HasCompactSupport.of_compactSpace _)]
    have hinner (Z : G) : (∫ W, (F (U * (Z * W * Z⁻¹)) - F U) ^ 2 ∂μ) =
        ∫ y, (F y - F U) ^ 2 ∂μ := by
      have hright := integral_mul_right_eq_self (μ := μ)
        (fun y => (F (U * (Z * y)) - F U) ^ 2) Z⁻¹
      simp only [mul_assoc] at hright ⊢
      rw [hright]
      exact (integral_mul_left_eq_self (μ := μ)
        (fun y => (F (U * y) - F U) ^ 2) Z).trans
        (integral_mul_left_eq_self (μ := μ) (fun y => (F y - F U) ^ 2) U)
    simp_rw [hinner]
    simp
  simp_rw [he]
  apply integral_integral_sq_sub_eq_two_variance
  exact hF.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- A uniform bound on averaged conjugated increments gives a variance bound. -/
theorem variance_le_of_haar_conjugated_increments (F : G → ℝ) (hF : Continuous F)
    (C : ℝ) (hC : ∀ W, (∫ U, ∫ Z,
      (F (U * (Z * W * Z⁻¹)) - F U) ^ 2 ∂μ ∂μ) ≤ C) : variance F μ ≤ C / 2 := by
  have hc : Continuous (fun W => ∫ U, ∫ Z,
      (F (U * (Z * W * Z⁻¹)) - F U) ^ 2 ∂μ ∂μ) := by
    apply compact_integral_continuous μ
    apply compact_integral_continuous μ
    fun_prop
  have h := integral_mono (μ := μ) (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (integrable_const C) hC
  rw [haar_conjugated_increment_variance μ F hF] at h
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at h
  linarith

end OperatorPhaseRetrieval

end
