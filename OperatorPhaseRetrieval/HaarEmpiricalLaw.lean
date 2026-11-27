import OperatorPhaseRetrieval.GaussianEmpiricalLaw
import OperatorPhaseRetrieval.FiniteEmpiricalLaw
import OperatorPhaseRetrieval.FiniteExpressionContinuity

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace OperatorPhaseRetrieval

/-- A concrete metric error for weak convergence to the circular Gaussian law. -/
def gaussianMarginalError (ν : ProbabilityMeasure ℂ) : ℝ :=
  dist (LevyProkhorov.probabilityMeasureHomeomorph ν)
    (LevyProkhorov.probabilityMeasureHomeomorph circularGaussian)

theorem gaussianMarginalError_continuous : Continuous gaussianMarginalError :=
  LevyProkhorov.probabilityMeasureHomeomorph.continuous.dist continuous_const

theorem gaussianMarginalError_nonneg (ν : ProbabilityMeasure ℂ) :
    0 ≤ gaussianMarginalError ν := dist_nonneg

@[simp] theorem gaussianMarginalError_self : gaussianMarginalError circularGaussian = 0 :=
  dist_self _

variable (ι : Type*) [Fintype ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

def finiteHaarLaw (U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) : ProbabilityMeasure ℂ :=
  finiteEmpiricalLaw (finiteHaarSeed ι U)

def finiteGaussianLaw (z : ι → ℂ) : ProbabilityMeasure ℂ :=
  finiteEmpiricalLaw (finiteGaussianSeed ι (WithLp.toLp 2 z))

theorem finiteHaarSeed_continuous : Continuous (finiteHaarSeed ι) := by
  apply continuous_pi
  intro i
  exact finiteExpression_coordinate_continuous ι .seed i

theorem finiteHaarLaw_continuous : Continuous (finiteHaarLaw ι) :=
  finiteEmpiricalLaw_continuous.comp (finiteHaarSeed_continuous ι)

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
theorem finiteGaussianLaw_error_measurable :
    Measurable (fun z => gaussianMarginalError (finiteGaussianLaw ι z)) := by
  have hc := gaussianMarginalError_continuous.comp
    (finiteEmpiricalLaw_continuous (ι := ι) (E := ℂ))
  exact hc.measurable.comp ((finiteGaussianSeed_measurable ι).comp
    (PiLp.continuous_toLp 2 (fun _ : ι => ℂ)).measurable)

/-- Equality of the exceptional-event probabilities in the Haar and iid Gaussian models. -/
theorem finiteHaarLaw_gaussian_probability (s : Set ℝ) (hs : MeasurableSet s) :
    (haarSixProbability ι : Measure _) {U | gaussianMarginalError (finiteHaarLaw ι U) ∈ s} =
    (Measure.pi (fun _ : ι => stdGaussian ℂ))
      {z | gaussianMarginalError (finiteGaussianLaw ι z) ∈ s} := by
  let f : (ι → ℂ) → ℝ := fun z => gaussianMarginalError (finiteEmpiricalLaw z)
  have hf : Measurable f :=
    (gaussianMarginalError_continuous.comp finiteEmpiricalLaw_continuous).measurable
  have hg : Measurable (fun z : ι → ℂ => finiteGaussianSeed ι (WithLp.toLp 2 z)) :=
    (finiteGaussianSeed_measurable ι).comp
      (PiLp.continuous_toLp 2 (fun _ : ι => ℂ)).measurable
  have he := congrArg (fun μ : Measure (ι → ℂ) => μ (f ⁻¹' s))
    (finiteHaarSeed_iid_gaussian_law ι)
  rw [Measure.map_apply (finiteHaarSeed_continuous ι).measurable (hf hs),
    Measure.map_apply hg (hf hs)] at he
  exact he

variable {ι}

theorem normalizedGaussian_empiricalLaw_eq (z : ℕ → ℂ) (n : ℕ) :
    empiricalLaw (fun i =>
      (Real.sqrt (empiricalAverage (fun y : ℂ => ‖y‖ ^ 2) z (n+1)))⁻¹ • z i) n =
      finiteGaussianLaw (Fin (n+1)) (fun i => z i) := by
  rw [empiricalLaw_eq_finiteEmpiricalLaw]
  unfold finiteGaussianLaw
  congr 1
  funext i
  rw [finiteGaussianSeed_empirical_normalization]
  simp only [Fintype.card_fin, empiricalAverage, smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun i => ‖z i‖ ^ 2) (n+1)]

theorem normalizedGaussian_error_tendstoInMeasure :
    TendstoInMeasure iidComplexGaussian
      (fun n z => gaussianMarginalError (finiteGaussianLaw (Fin (n+1)) (fun i => z i)))
      atTop (fun _ => 0) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    have hm : Measurable (fun z : ℕ → ℂ => fun i : Fin (n+1) => z i) :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply (i : ℕ))
    exact ((finiteGaussianLaw_error_measurable (Fin (n+1))).comp hm).aestronglyMeasurable
  · filter_upwards [normalizedGaussian_empiricalLaw_tendsto] with z hz
    have h := gaussianMarginalError_continuous.continuousAt.tendsto.comp hz
    simpa only [normalizedGaussian_empiricalLaw_eq, gaussianMarginalError_self, Function.comp_def] using h

/-- The Gaussian marginal condition holds in probability for the
actual six-Haar finite models, without any concentration assumption. -/
theorem finiteHaarLaw_error_probability_tendsto (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (haarSixProbability (Fin (n+1)) : Measure _)
      {U | ε ≤ gaussianMarginalError (finiteHaarLaw (Fin (n+1)) U)}) atTop (𝓝 0) := by
  have h := tendstoInMeasure_iff_dist.mp normalizedGaussian_error_tendstoInMeasure ε hε
  simp only [dist_zero_right, Real.norm_eq_abs,
    abs_of_nonneg (gaussianMarginalError_nonneg _)] at h
  have he (n : ℕ) :
      (haarSixProbability (Fin (n+1)) : Measure _)
        {U | ε ≤ gaussianMarginalError (finiteHaarLaw (Fin (n+1)) U)} =
      iidComplexGaussian
        {z | ε ≤ gaussianMarginalError (finiteGaussianLaw (Fin (n+1)) (fun i => z i))} := by
    have hH := finiteHaarLaw_gaussian_probability (Fin (n+1)) (Set.Ici ε) measurableSet_Ici
    simp only [Set.mem_Ici] at hH
    rw [hH, ← iidComplexGaussian_prefix_law (n+1)]
    have hm : Measurable (fun z : ℕ → ℂ => fun i : Fin (n+1) => z i) :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply (i : ℕ))
    have hs : MeasurableSet {z : Fin (n+1) → ℂ |
        ε ≤ gaussianMarginalError (finiteGaussianLaw (Fin (n+1)) z)} :=
      measurableSet_le measurable_const (finiteGaussianLaw_error_measurable (Fin (n+1)))
    rw [Measure.map_apply hm hs]
    rfl
  simpa only [he] using h

theorem finiteHaarLaw_error_probability_eventually (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ n, N ≤ n → (haarSixProbability (Fin (n+1)) : Measure _)
      {U | ε ≤ gaussianMarginalError (finiteHaarLaw (Fin (n+1)) U)} ≤ 1 / 8 := by
  exact ENNReal.tendsto_atTop_zero.mp (finiteHaarLaw_error_probability_tendsto ε hε)
    (1/8) (by norm_num)

end OperatorPhaseRetrieval

end
