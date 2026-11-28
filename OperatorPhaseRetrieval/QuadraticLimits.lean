module

public import OperatorPhaseRetrieval.JointLawLimit

@[expose] public section

/-!
# Unbounded observables under weak convergence

Uniform fourth moments are used in the limit construction to pass quadratic integrals
to the joint weak limit. The main estimate here is proved by continuous
truncation, with an explicit uniform bound for the truncation error.
-/

noncomputable section

open MeasureTheory Filter BoundedContinuousFunction
open scoped ENNReal NNReal Topology

namespace OperatorPhaseRetrieval

variable {X : Type*} [TopologicalSpace X]

/-- Truncate a nonnegative continuous function to a bounded continuous function. -/
def nonnegativeTruncation (f : X → ℝ) (hf : Continuous f) (hpos : ∀ x, 0 ≤ f x)
    (R : ℝ) (hR : 0 ≤ R) : X →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun x => min (f x) R, hf.min continuous_const⟩ R (by
    intro x y
    change dist (min (f x) R) (min (f y) R) ≤ R
    rw [Real.dist_eq, abs_le]
    constructor <;>
      linarith [le_min (hpos x) hR, le_min (hpos y) hR, min_le_right (f x) R,
        min_le_right (f y) R])

theorem nonnegativeTruncation_apply (f : X → ℝ) (hf : Continuous f) (hpos : ∀ x, 0 ≤ f x)
    (R : ℝ) (hR : 0 ≤ R) (x : X) :
    nonnegativeTruncation f hf hpos R hR x = min (f x) R := rfl

variable [MeasurableSpace X] [OpensMeasurableSpace X]

/-- Truncation loses at most the second moment divided by the truncation level. -/
theorem integral_truncation_error_le (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Continuous f) (hpos : ∀ x, 0 ≤ f x)
    (hfi : Integrable (fun x => f x ^ 2) μ)
    (M R : ℝ) (hM : (∫ x, f x ^ 2 ∂μ) ≤ M) (hR : 0 < R) :
    dist (∫ x, f x ∂μ) (∫ x, nonnegativeTruncation f hf hpos R hR.le x ∂μ) ≤ M / R := by
  have hi : Integrable f μ :=
    ((memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr hfi).integrable (by norm_num)
  let g := nonnegativeTruncation f hf hpos R hR.le
  have hg : Integrable g μ := g.integrable μ
  have hnonneg x : 0 ≤ f x - g x := sub_nonneg.mpr (min_le_left _ _)
  have hpoint x : f x - g x ≤ f x ^ 2 / R := by
    change f x - min (f x) R ≤ f x ^ 2 / R
    by_cases hx : f x ≤ R
    · rw [min_eq_left hx, sub_self]
      positivity
    · rw [min_eq_right (le_of_not_ge hx)]
      apply (le_div_iff₀ hR).mpr
      nlinarith [sq_nonneg (f x - R), mul_nonneg hR.le (hpos x)]
  have hbound := integral_mono (hi.sub hg) (hfi.div_const R) hpoint
  change (∫ x, f x - g x ∂μ) ≤ ∫ x, f x ^ 2 / R ∂μ at hbound
  rw [integral_sub hi hg, integral_div] at hbound
  rw [Real.dist_eq, abs_of_nonneg (by
    rw [← integral_sub hi hg]
    exact integral_nonneg hnonneg)]
  exact hbound.trans (div_le_div_of_nonneg_right hM hR.le)

variable [HasOuterApproxClosed X]

/-- Weak convergence plus uniform second moments of a continuous nonnegative
observable implies convergence of its (possibly unbounded) integrals. -/
theorem integral_tendsto_of_uniform_second_moment
    {P : ℕ → ProbabilityMeasure X} {Q : ProbabilityMeasure X}
    (hlim : Tendsto P atTop (𝓝 Q))
    (f : X → ℝ) (hf : Continuous f) (hpos : ∀ x, 0 ≤ f x)
    (M : ℝ≥0)
    (hM : ∀ n, ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂(P n : Measure X) ≤ M) :
    Tendsto (fun n => ∫ x, f x ∂(P n : Measure X)) atTop
      (𝓝 (∫ x, f x ∂(Q : Measure X))) := by
  have hQ : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂(Q : Measure X) ≤ M := by
    have h := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
      (hf.pow 2) (fun x => sq_nonneg (f x))
      (fun _ hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG)
    exact h.trans ((liminf_le_liminf (Eventually.of_forall hM)).trans_eq (liminf_const _))
  have hb (μ : Measure X) (hμ : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ ≤ M) :
      Integrable (fun x => f x ^ 2) μ ∧ (∫ x, f x ^ 2 ∂μ) ≤ M := by
    have hn : 0 ≤ᵐ[μ] fun x => f x ^ 2 := Eventually.of_forall fun x => sq_nonneg (f x)
    have hi : Integrable (fun x => f x ^ 2) μ :=
      (lintegral_ofReal_ne_top_iff_integrable (hf.pow 2).aestronglyMeasurable hn).mp
      (ne_top_of_le_ne_top ENNReal.coe_ne_top hμ)
    refine ⟨hi, ?_⟩
    apply (ENNReal.ofReal_le_ofReal_iff M.coe_nonneg).mp
    rw [ofReal_integral_eq_lintegral_ofReal hi hn, ENNReal.ofReal_coe_nnreal]
    exact hμ
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  let R : ℝ := 4 * ((M : ℝ) + 1) / ε
  have hR : 0 < R := by dsimp [R]; positivity
  have hsmall : (M : ℝ) / R ≤ ε / 4 := by
    apply (div_le_iff₀ hR).mpr
    calc
      (M : ℝ) ≤ M + 1 := by linarith
      _ = ε / 4 * R := by dsimp [R]; field_simp
  let g := nonnegativeTruncation f hf hpos R hR.le
  have hg := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim g
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hg (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hnerr := integral_truncation_error_le (P n : Measure X) f hf hpos
    (hb _ (hM n)).1 M R (hb _ (hM n)).2 hR
  have hQerr := integral_truncation_error_le (Q : Measure X) f hf hpos
    (hb _ hQ).1 M R (hb _ hQ).2 hR
  have ht₁ := dist_triangle (∫ x, f x ∂(P n : Measure X))
    (∫ x, g x ∂(P n : Measure X)) (∫ x, f x ∂(Q : Measure X))
  have ht₂ := dist_triangle (∫ x, g x ∂(P n : Measure X))
    (∫ x, g x ∂(Q : Measure X)) (∫ x, f x ∂(Q : Measure X))
  rw [dist_comm (∫ x, f x ∂(Q : Measure X))] at hQerr
  change dist (∫ x, f x ∂(P n : Measure X)) (∫ x, g x ∂(P n : Measure X)) ≤ M / R at hnerr
  change dist (∫ x, g x ∂(Q : Measure X)) (∫ x, f x ∂(Q : Measure X)) ≤ M / R at hQerr
  linarith [hN n hn]

omit [HasOuterApproxClosed X] in
/-- A finite real second moment supplies the integrability needed for
positive/negative-part decompositions of an unbounded observable. -/
theorem integrable_of_real_second_moment_bound
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) (hf : Continuous f)
    (M : ℝ≥0) (hM : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ ≤ M) : Integrable f μ := by
  have hi : Integrable (fun x => f x ^ 2) μ :=
    (lintegral_ofReal_ne_top_iff_integrable (hf.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => sq_nonneg (f x))).mp
      (ne_top_of_le_ne_top ENNReal.coe_ne_top hM)
  exact ((memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr hi).integrable (by norm_num)

/-- The weak-integral convergence criterion also holds for real observables
of either sign. -/
theorem real_integral_tendsto_of_uniform_second_moment
    {P : ℕ → ProbabilityMeasure X} {Q : ProbabilityMeasure X}
    (hlim : Tendsto P atTop (𝓝 Q)) (f : X → ℝ) (hf : Continuous f) (M : ℝ≥0)
    (hM : ∀ n, ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂(P n : Measure X) ≤ M) :
    Tendsto (fun n => ∫ x, f x ∂(P n : Measure X)) atTop
      (𝓝 (∫ x, f x ∂(Q : Measure X))) := by
  have hpoint (a : ℝ) : max a 0 ^ 2 ≤ a ^ 2 := by
    rcases le_total 0 a with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h, zero_pow (by decide : 2 ≠ 0)]
      exact sq_nonneg a
  have hp := integral_tendsto_of_uniform_second_moment hlim
    (fun x => max (f x) 0) (hf.max continuous_const) (fun _ => le_max_right _ _) M
    (fun n => (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hpoint (f x))).trans (hM n))
  have hn := integral_tendsto_of_uniform_second_moment hlim
    (fun x => max (-f x) 0) (hf.neg.max continuous_const) (fun _ => le_max_right _ _) M
    (fun n => (lintegral_mono fun x => ENNReal.ofReal_le_ofReal
      (by simpa only [neg_sq] using hpoint (-f x))).trans (hM n))
  have hQ : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂(Q : Measure X) ≤ M := by
    have h := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
      (hf.pow 2) (fun x => sq_nonneg (f x))
      (fun _ hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG)
    exact h.trans ((liminf_le_liminf (Eventually.of_forall hM)).trans_eq (liminf_const _))
  have he (μ : Measure X) [IsFiniteMeasure μ]
      (hμ : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ ≤ M) :
      (∫ x, max (f x) 0 ∂μ) - (∫ x, max (-f x) 0 ∂μ) = ∫ x, f x ∂μ := by
    have hi := integrable_of_real_second_moment_bound μ f hf M hμ
    rw [← integral_sub hi.pos_part hi.neg_part]
    simp_rw [max_zero_sub_max_neg_zero_eq_self]
  have h := hp.sub hn
  rw [he _ hQ] at h
  exact h.congr' (Eventually.of_forall fun n => he _ (hM n))

omit [HasOuterApproxClosed X] in
/-- A norm-second-moment bound makes a continuous complex observable integrable. -/
theorem integrable_of_complex_second_moment_bound
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℂ) (hf : Continuous f)
    (M : ℝ≥0) (hM : ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ ≤ M) : Integrable f μ := by
  have hi : Integrable (fun x => ‖f x‖ ^ 2) μ :=
    (lintegral_ofReal_ne_top_iff_integrable (hf.norm.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => sq_nonneg ‖f x‖)).mp
      (ne_top_of_le_ne_top ENNReal.coe_ne_top hM)
  exact ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr hi).integrable (by norm_num)

/-- Uniform norm-second-moment control also gives weak-integral convergence
for complex observables, by applying the real result to both components. -/
theorem complex_integral_tendsto_of_uniform_second_moment
    {P : ℕ → ProbabilityMeasure X} {Q : ProbabilityMeasure X}
    (hlim : Tendsto P atTop (𝓝 Q)) (f : X → ℂ) (hf : Continuous f) (M : ℝ≥0)
    (hM : ∀ n, ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂(P n : Measure X) ≤ M) :
    Tendsto (fun n => ∫ x, f x ∂(P n : Measure X)) atTop
      (𝓝 (∫ x, f x ∂(Q : Measure X))) := by
  have hreal x : (f x).re ^ 2 ≤ ‖f x‖ ^ 2 := by
    nlinarith [Complex.sq_norm_sub_sq_re (f x), sq_nonneg (f x).im]
  have himag x : (f x).im ^ 2 ≤ ‖f x‖ ^ 2 := by
    nlinarith [Complex.sq_norm_sub_sq_im (f x), sq_nonneg (f x).re]
  have hr := real_integral_tendsto_of_uniform_second_moment hlim _
    (Complex.continuous_re.comp hf) M
    (fun n => (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hreal x)).trans (hM n))
  have hi := real_integral_tendsto_of_uniform_second_moment hlim _
    (Complex.continuous_im.comp hf) M
    (fun n => (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (himag x)).trans (hM n))
  have hQ : ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂(Q : Measure X) ≤ M := by
    have h := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
      (hf.norm.pow 2) (fun x => sq_nonneg ‖f x‖)
      (fun _ hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG)
    exact h.trans ((liminf_le_liminf (Eventually.of_forall hM)).trans_eq (liminf_const _))
  have hPi n := integrable_of_complex_second_moment_bound (P n : Measure X) f hf M (hM n)
  have hQi := integrable_of_complex_second_moment_bound (Q : Measure X) f hf M hQ
  change Tendsto (fun n => ∫ x, RCLike.re (f x) ∂(P n : Measure X)) atTop
    (𝓝 (∫ x, RCLike.re (f x) ∂(Q : Measure X))) at hr
  change Tendsto (fun n => ∫ x, RCLike.im (f x) ∂(P n : Measure X)) atTop
    (𝓝 (∫ x, RCLike.im (f x) ∂(Q : Measure X))) at hi
  simp_rw [integral_re (hPi _), integral_re hQi] at hr
  simp_rw [integral_im (hPi _), integral_im hQi] at hi
  have h := hr.ofReal.add (hi.ofReal.mul_const Complex.I)
  simpa only [RCLike.re_eq_complex_re, RCLike.im_eq_complex_im, Complex.re_add_im] using h

/-- Coordinate fourth moments give convergence of the squared `L²` norms. -/
theorem jointLaw_coordinate_sq_integral_tendsto
    {P : ℕ → ProbabilityMeasure (ℕ → ℂ)} {Q : ProbabilityMeasure (ℕ → ℂ)}
    (hlim : Tendsto P atTop (𝓝 Q)) (r : ℕ) (M : ℝ≥0)
    (hM : ∀ n, ∫⁻ z, ENNReal.ofReal (‖z r‖ ^ 4) ∂(P n : Measure (ℕ → ℂ)) ≤ M) :
    Tendsto (fun n => ∫ z, ‖z r‖ ^ 2 ∂(P n : Measure (ℕ → ℂ))) atTop
      (𝓝 (∫ z, ‖z r‖ ^ 2 ∂(Q : Measure (ℕ → ℂ)))) := by
  apply integral_tendsto_of_uniform_second_moment hlim _ ((continuous_apply r).norm.pow 2)
    (fun z => sq_nonneg ‖z r‖) M
  intro n
  simpa only [Pi.pow_apply, ← pow_mul] using hM n

/-- The quadratic modulus-difference observable has its second moment
controlled by the two coordinate fourth moments. -/
theorem modulusDifference_second_moment_le
    (μ : Measure (ℕ → ℂ)) (r s : ℕ) (M N : ℝ≥0)
    (hM : ∫⁻ z, ENNReal.ofReal (‖z r‖ ^ 4) ∂μ ≤ M)
    (hN : ∫⁻ z, ENNReal.ofReal (‖z s‖ ^ 4) ∂μ ≤ N) :
    ∫⁻ z, ENNReal.ofReal (((‖z r‖ - ‖z s‖) ^ 2) ^ 2) ∂μ ≤
      ((2 * (M + N) : ℝ≥0) : ℝ≥0∞) := by
  have hpoint (z : ℕ → ℂ) : ((‖z r‖ - ‖z s‖) ^ 2) ^ 2 ≤
      2 * (‖z r‖ ^ 4 + ‖z s‖ ^ 4) := by
    have hsq : (‖z r‖ - ‖z s‖) ^ 2 ≤ ‖z r‖ ^ 2 + ‖z s‖ ^ 2 := by
      nlinarith [mul_nonneg (norm_nonneg (z r)) (norm_nonneg (z s))]
    calc
      ((‖z r‖ - ‖z s‖) ^ 2) ^ 2 ≤ (‖z r‖ ^ 2 + ‖z s‖ ^ 2) ^ 2 := by
        gcongr
      _ ≤ _ := by nlinarith [sq_nonneg (‖z r‖ ^ 2 - ‖z s‖ ^ 2)]
  calc
    ∫⁻ z, ENNReal.ofReal (((‖z r‖ - ‖z s‖) ^ 2) ^ 2) ∂μ ≤
        ∫⁻ z, ENNReal.ofReal (2 * (‖z r‖ ^ 4 + ‖z s‖ ^ 4)) ∂μ :=
      lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hpoint z)
    _ = 2 * ((∫⁻ z, ENNReal.ofReal (‖z r‖ ^ 4) ∂μ) +
        ∫⁻ z, ENNReal.ofReal (‖z s‖ ^ 4) ∂μ) := by
      have he (z : ℕ → ℂ) : ENNReal.ofReal (2 * (‖z r‖ ^ 4 + ‖z s‖ ^ 4)) =
          2 * (ENNReal.ofReal (‖z r‖ ^ 4) + ENNReal.ofReal (‖z s‖ ^ 4)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_add (by positivity) (by positivity)]
        norm_num
      simp_rw [he]
      rw [lintegral_const_mul' _ _ (by norm_num),
        lintegral_add_left (((measurable_pi_apply r).norm.pow_const 4).ennreal_ofReal)]
    _ ≤ _ := by
      push_cast
      gcongr

/-- Coordinate fourth moments also give convergence of squared distances
between magnitudes, the measurement quantities needed by Theorem B. -/
theorem jointLaw_modulusDifference_integral_tendsto
    {P : ℕ → ProbabilityMeasure (ℕ → ℂ)} {Q : ProbabilityMeasure (ℕ → ℂ)}
    (hlim : Tendsto P atTop (𝓝 Q)) (r s : ℕ) (M N : ℝ≥0)
    (hM : ∀ n, ∫⁻ z, ENNReal.ofReal (‖z r‖ ^ 4) ∂(P n : Measure (ℕ → ℂ)) ≤ M)
    (hN : ∀ n, ∫⁻ z, ENNReal.ofReal (‖z s‖ ^ 4) ∂(P n : Measure (ℕ → ℂ)) ≤ N) :
    Tendsto (fun n => ∫ z, (‖z r‖ - ‖z s‖) ^ 2 ∂(P n : Measure (ℕ → ℂ))) atTop
      (𝓝 (∫ z, (‖z r‖ - ‖z s‖) ^ 2 ∂(Q : Measure (ℕ → ℂ)))) := by
  exact integral_tendsto_of_uniform_second_moment hlim _
    (((continuous_apply r).norm.sub (continuous_apply s).norm).pow 2)
    (fun z => sq_nonneg (‖z r‖ - ‖z s‖)) (2 * (M + N))
    (fun n => modulusDifference_second_moment_le _ r s M N (hM n) (hN n))

/-- The coordinate product defining a complex inner product has uniformly
bounded second moment when both coordinate fourth moments are bounded. -/
theorem coordinateProduct_second_moment_le
    (μ : Measure (ℕ → ℂ)) (r s : ℕ) (M N : ℝ≥0)
    (hM : ∫⁻ z, ENNReal.ofReal (‖z r‖ ^ 4) ∂μ ≤ M)
    (hN : ∫⁻ z, ENNReal.ofReal (‖z s‖ ^ 4) ∂μ ≤ N) :
    ∫⁻ z, ENNReal.ofReal (‖star (z r) * z s‖ ^ 2) ∂μ ≤ ((M + N : ℝ≥0) : ℝ≥0∞) := by
  have hpoint (z : ℕ → ℂ) : ‖star (z r) * z s‖ ^ 2 ≤ ‖z r‖ ^ 4 + ‖z s‖ ^ 4 := by
    rw [norm_mul, norm_star, mul_pow]
    nlinarith [sq_nonneg (‖z r‖ ^ 2 - ‖z s‖ ^ 2), sq_nonneg (‖z r‖ ^ 2),
      sq_nonneg (‖z s‖ ^ 2)]
  calc
    ∫⁻ z, ENNReal.ofReal (‖star (z r) * z s‖ ^ 2) ∂μ ≤
        ∫⁻ z, ENNReal.ofReal (‖z r‖ ^ 4 + ‖z s‖ ^ 4) ∂μ :=
      lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hpoint z)
    _ = (∫⁻ z, ENNReal.ofReal (‖z r‖ ^ 4) ∂μ) +
        ∫⁻ z, ENNReal.ofReal (‖z s‖ ^ 4) ∂μ := by
      have he (z : ℕ → ℂ) : ENNReal.ofReal (‖z r‖ ^ 4 + ‖z s‖ ^ 4) =
          ENNReal.ofReal (‖z r‖ ^ 4) + ENNReal.ofReal (‖z s‖ ^ 4) :=
        ENNReal.ofReal_add (by positivity) (by positivity)
      simp_rw [he]
      exact lintegral_add_left (((measurable_pi_apply r).norm.pow_const 4).ennreal_ofReal) _
    _ ≤ _ := by
      push_cast
      exact add_le_add hM hN

/-- Convergence of the complex inner-product integrals in the limit construction. -/
theorem jointLaw_coordinate_inner_integral_tendsto
    {P : ℕ → ProbabilityMeasure (ℕ → ℂ)} {Q : ProbabilityMeasure (ℕ → ℂ)}
    (hlim : Tendsto P atTop (𝓝 Q)) (r s : ℕ) (M N : ℝ≥0)
    (hM : ∀ n, ∫⁻ z, ENNReal.ofReal (‖z r‖ ^ 4) ∂(P n : Measure (ℕ → ℂ)) ≤ M)
    (hN : ∀ n, ∫⁻ z, ENNReal.ofReal (‖z s‖ ^ 4) ∂(P n : Measure (ℕ → ℂ)) ≤ N) :
    Tendsto (fun n => ∫ z, star (z r) * z s ∂(P n : Measure (ℕ → ℂ))) atTop
      (𝓝 (∫ z, star (z r) * z s ∂(Q : Measure (ℕ → ℂ)))) := by
  exact complex_integral_tendsto_of_uniform_second_moment hlim _
    ((continuous_apply r).star.mul (continuous_apply s)) (M + N)
    (fun n => coordinateProduct_second_moment_le _ r s M N (hM n) (hN n))

end OperatorPhaseRetrieval

end
