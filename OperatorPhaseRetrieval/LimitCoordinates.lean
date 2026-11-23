import OperatorPhaseRetrieval.QuadraticLimits
import OperatorPhaseRetrieval.StabilityLimits

/-! # Actual `L²` coordinates and convergence of their phase and magnitude distances -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology InnerProductSpace

namespace OperatorPhaseRetrieval

/-- A finite fourth moment puts a coordinate in the actual `L²` space. -/
theorem coordinate_memLp_of_fourth_moment (μ : Measure (ℕ → ℂ)) [IsFiniteMeasure μ]
    (r : ℕ) (M : ℝ≥0)
    (hM : ∫⁻ z, ENNReal.ofReal (‖z r‖ ^ 4) ∂μ ≤ M) :
    MemLp (fun z : ℕ → ℂ => z r) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm (measurable_pi_apply r).aestronglyMeasurable).mpr
  apply integrable_of_real_second_moment_bound μ _ ((continuous_apply r).norm.pow 2) M
  simpa only [Pi.pow_apply, ← pow_mul] using hM

/-- The coordinate functions as elements of the actual Mathlib `L²` space. -/
def jointCoordinate (μ : Measure (ℕ → ℂ))
    (h : ∀ r : ℕ, MemLp (fun z : ℕ → ℂ => z r) 2 μ) (r : ℕ) : L2 μ :=
  (h r).toLp (fun z => z r)

theorem jointCoordinate_coeFn (μ : Measure (ℕ → ℂ))
    (h : ∀ r : ℕ, MemLp (fun z : ℕ → ℂ => z r) 2 μ) (r : ℕ) :
    (jointCoordinate μ h r : (ℕ → ℂ) → ℂ) =ᵐ[μ] fun z => z r :=
  (h r).coeFn_toLp

theorem jointCoordinate_norm_sq (μ : Measure (ℕ → ℂ))
    (h : ∀ r : ℕ, MemLp (fun z : ℕ → ℂ => z r) 2 μ) (r : ℕ) :
    ‖jointCoordinate μ h r‖ ^ 2 = ∫ z, ‖z r‖ ^ 2 ∂μ := by
  rw [l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [jointCoordinate_coeFn μ h r] with z hz
  rw [hz]

theorem jointCoordinate_inner (μ : Measure (ℕ → ℂ))
    (h : ∀ r : ℕ, MemLp (fun z : ℕ → ℂ => z r) 2 μ) (r s : ℕ) :
    ⟪jointCoordinate μ h r, jointCoordinate μ h s⟫_ℂ = ∫ z, star (z r) * z s ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [jointCoordinate_coeFn μ h r, jointCoordinate_coeFn μ h s] with z hr hs
  rw [hr, hs]
  simp [RCLike.inner_apply, mul_comm]

theorem jointCoordinate_magnitudeDistance_sq (μ : Measure (ℕ → ℂ))
    (h : ∀ r : ℕ, MemLp (fun z : ℕ → ℂ => z r) 2 μ) (r s : ℕ) :
    ‖magnitude (jointCoordinate μ h r) - magnitude (jointCoordinate μ h s)‖ ^ 2 =
      ∫ z, (‖z r‖ - ‖z s‖) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (magnitude (jointCoordinate μ h r)) (magnitude (jointCoordinate μ h s)),
    magnitude_coeFn (jointCoordinate μ h r), magnitude_coeFn (jointCoordinate μ h s),
    jointCoordinate_coeFn μ h r, jointCoordinate_coeFn μ h s] with z hsub hr hs hcr hcs
  simp only [Pi.sub_apply] at hsub
  rw [hsub, hr, hs, hcr, hcs, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- Gram entries of the actual `L²` coordinate vectors converge. -/
theorem jointCoordinate_inner_tendsto
    {P : ℕ → ProbabilityMeasure (ℕ → ℂ)} {Q : ProbabilityMeasure (ℕ → ℂ)}
    (hlim : Tendsto P atTop (𝓝 Q))
    (hP : ∀ n r, MemLp (fun z : ℕ → ℂ => z r) 2 (P n : Measure (ℕ → ℂ)))
    (hQ : ∀ r, MemLp (fun z : ℕ → ℂ => z r) 2 (Q : Measure (ℕ → ℂ)))
    (M : ℕ → ℝ≥0)
    (hM : ∀ n r, ∫⁻ z, ENNReal.ofReal (‖z r‖ ^ 4) ∂(P n : Measure (ℕ → ℂ)) ≤ M r)
    (r s : ℕ) :
    Tendsto (fun n => ⟪jointCoordinate (P n) (hP n) r, jointCoordinate (P n) (hP n) s⟫_ℂ)
      atTop (𝓝 ⟪jointCoordinate Q hQ r, jointCoordinate Q hQ s⟫_ℂ) := by
  simpa only [jointCoordinate_inner] using
    jointLaw_coordinate_inner_integral_tendsto hlim r s (M r) (M s)
      (fun n => hM n r) (fun n => hM n s)

/-- The raw fourth-moment bounds give convergence of phase distances between
the actual `L²` coordinate vectors, whose ambient measures vary with `n`. -/
theorem jointCoordinate_phaseDistance_tendsto
    {P : ℕ → ProbabilityMeasure (ℕ → ℂ)} {Q : ProbabilityMeasure (ℕ → ℂ)}
    (hlim : Tendsto P atTop (𝓝 Q))
    (hP : ∀ n r, MemLp (fun z : ℕ → ℂ => z r) 2 (P n : Measure (ℕ → ℂ)))
    (hQ : ∀ r, MemLp (fun z : ℕ → ℂ => z r) 2 (Q : Measure (ℕ → ℂ)))
    (M : ℕ → ℝ≥0)
    (hM : ∀ n r, ∫⁻ z, ENNReal.ofReal (‖z r‖ ^ 4) ∂(P n : Measure (ℕ → ℂ)) ≤ M r)
    (r s : ℕ) :
    Tendsto (fun n => phaseDistance (jointCoordinate (P n) (hP n) r)
        (jointCoordinate (P n) (hP n) s)) atTop
      (𝓝 (phaseDistance (jointCoordinate Q hQ r) (jointCoordinate Q hQ s))) := by
  apply phaseDistance_tendsto_of_norm_inner
    (fun n => L2 (P n : Measure (ℕ → ℂ)))
  · simpa only [jointCoordinate_norm_sq] using
      jointLaw_coordinate_sq_integral_tendsto hlim r (M r) (fun n => hM n r)
  · simpa only [jointCoordinate_norm_sq] using
      jointLaw_coordinate_sq_integral_tendsto hlim s (M s) (fun n => hM n s)
  · simpa only [jointCoordinate_inner] using
      jointLaw_coordinate_inner_integral_tendsto hlim r s (M r) (M s)
        (fun n => hM n r) (fun n => hM n s)

/-- The magnitude distances converge too, after taking the nonnegative
square roots of the quadratic integrals. -/
theorem jointCoordinate_magnitudeDistance_tendsto
    {P : ℕ → ProbabilityMeasure (ℕ → ℂ)} {Q : ProbabilityMeasure (ℕ → ℂ)}
    (hlim : Tendsto P atTop (𝓝 Q))
    (hP : ∀ n r, MemLp (fun z : ℕ → ℂ => z r) 2 (P n : Measure (ℕ → ℂ)))
    (hQ : ∀ r, MemLp (fun z : ℕ → ℂ => z r) 2 (Q : Measure (ℕ → ℂ)))
    (M : ℕ → ℝ≥0)
    (hM : ∀ n r, ∫⁻ z, ENNReal.ofReal (‖z r‖ ^ 4) ∂(P n : Measure (ℕ → ℂ)) ≤ M r)
    (r s : ℕ) :
    Tendsto (fun n => ‖magnitude (jointCoordinate (P n) (hP n) r) -
        magnitude (jointCoordinate (P n) (hP n) s)‖) atTop
      (𝓝 ‖magnitude (jointCoordinate Q hQ r) - magnitude (jointCoordinate Q hQ s)‖) := by
  have h := jointLaw_modulusDifference_integral_tendsto hlim r s (M r) (M s)
    (fun n => hM n r) (fun n => hM n s)
  simp_rw [← jointCoordinate_magnitudeDistance_sq _ (hP _) r s] at h
  rw [← jointCoordinate_magnitudeDistance_sq _ hQ r s] at h
  simpa only [Real.sqrt_sq (norm_nonneg _)] using h.sqrt

/-- Replacing each component by its norm leaves a finite product's maximum norm unchanged. -/
theorem norm_component_norms {ι : Type*} [Fintype ι]
    {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)] (v : ∀ i, E i) :
    ‖fun i => ‖v i‖‖ = ‖v‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
    intro i
    simpa only [norm_norm] using norm_le_pi_norm v i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (fun i => ‖v i‖))).mpr
    intro i
    simpa only [norm_norm] using norm_le_pi_norm (fun i => ‖v i‖) i

/-- The finite collection of formal measurement expressions, before its
action is extended to all of `L²`. -/
def coordinateMeasurementDistance {ι : Type*} [Fintype ι]
    (μ : Measure (ℕ → ℂ)) (h : ∀ r : ℕ, MemLp (fun z : ℕ → ℂ => z r) 2 μ)
    (a : ι → ℕ → ℕ) (r s : ℕ) : ℝ :=
  ‖fun j => magnitude (jointCoordinate μ h (a j r)) - magnitude (jointCoordinate μ h (a j s))‖

/-- The maximum of finitely many measurement distances passes to the limit. -/
theorem coordinateMeasurementDistance_tendsto {ι : Type*} [Fintype ι]
    {P : ℕ → ProbabilityMeasure (ℕ → ℂ)} {Q : ProbabilityMeasure (ℕ → ℂ)}
    (hlim : Tendsto P atTop (𝓝 Q))
    (hP : ∀ n r, MemLp (fun z : ℕ → ℂ => z r) 2 (P n : Measure (ℕ → ℂ)))
    (hQ : ∀ r, MemLp (fun z : ℕ → ℂ => z r) 2 (Q : Measure (ℕ → ℂ)))
    (M : ℕ → ℝ≥0)
    (hM : ∀ n r, ∫⁻ z, ENNReal.ofReal (‖z r‖ ^ 4) ∂(P n : Measure (ℕ → ℂ)) ≤ M r)
    (a : ι → ℕ → ℕ) (r s : ℕ) :
    Tendsto (fun n => coordinateMeasurementDistance (P n) (hP n) a r s) atTop
      (𝓝 (coordinateMeasurementDistance Q hQ a r s)) := by
  have h : Tendsto (fun n => fun j =>
      ‖magnitude (jointCoordinate (P n) (hP n) (a j r)) -
        magnitude (jointCoordinate (P n) (hP n) (a j s))‖) atTop
      (𝓝 (fun j => ‖magnitude (jointCoordinate Q hQ (a j r)) -
        magnitude (jointCoordinate Q hQ (a j s))‖)) :=
    tendsto_pi_nhds.mpr fun j =>
      jointCoordinate_magnitudeDistance_tendsto hlim hP hQ M hM (a j r) (a j s)
  simpa only [norm_component_norms, coordinateMeasurementDistance] using h.norm

end OperatorPhaseRetrieval

end
