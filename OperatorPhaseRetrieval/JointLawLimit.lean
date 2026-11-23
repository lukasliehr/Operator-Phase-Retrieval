import OperatorPhaseRetrieval.ModelSelection
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Tightness and weak limits of joint coordinate laws

The joint laws in Section 4.5 live on `ℂ^ℕ` with its product topology.
Uniform second moments of each coordinate imply tightness of these laws.
The probability measures are inputs here; constructing the finite Haar models
and the unitary operators on the limiting space are separate obligations.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace OperatorPhaseRetrieval

/-- Markov's inequality with a radius chosen from the second moment. -/
theorem coordinate_tail_le {P : Measure (ℕ → ℂ)} (r : ℕ) (M ε : ℝ≥0)
    (hε : 0 < ε)
    (hM : ∫⁻ z, ENNReal.ofReal (‖z r‖ ^ 2) ∂P ≤ M) :
    P {z | Real.sqrt (((1 + M) / ε : ℝ≥0) : ℝ) < ‖z r‖} ≤ ε := by
  let T : ℝ≥0 := (1 + M) / ε
  have hT : 0 < T := div_pos (by positivity) hε
  have hratio : M / T ≤ ε := by
    apply (div_le_iff₀ hT).mpr
    have he : ε * T = 1 + M := by
      dsimp [T]
      rw [mul_div_cancel₀ _ hε.ne']
    rw [he]
    simp
  calc
    P {z | Real.sqrt (T : ℝ) < ‖z r‖} ≤
        P {z | (T : ℝ≥0∞) ≤ ENNReal.ofReal (‖z r‖ ^ 2)} := by
      apply measure_mono
      intro z hz
      change Real.sqrt (T : ℝ) < ‖z r‖ at hz
      change (T : ℝ≥0∞) ≤ ENNReal.ofReal (‖z r‖ ^ 2)
      rw [← ENNReal.ofReal_coe_nnreal]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [Real.sq_sqrt T.coe_nonneg, Real.sqrt_nonneg (T : ℝ), norm_nonneg (z r)]
    _ ≤ (∫⁻ z, ENNReal.ofReal (‖z r‖ ^ 2) ∂P) / T :=
      meas_ge_le_lintegral_div
        (((measurable_pi_apply r).norm.pow_const 2).ennreal_ofReal.aemeasurable)
        (by exact_mod_cast hT.ne') ENNReal.coe_ne_top
    _ ≤ (M : ℝ≥0∞) / T := ENNReal.div_le_div_right hM _
    _ = ↑(M / T) := (ENNReal.coe_div hT.ne').symm
    _ ≤ ε := ENNReal.coe_le_coe.mpr hratio

/-- Uniform coordinate second moments control a compact product of balls.
No independence of the coordinates is required. -/
theorem jointLaws_tight_of_second_moments
    (P : ℕ → ProbabilityMeasure (ℕ → ℂ)) (M : ℕ → ℝ≥0)
    (hM : ∀ n r, ∫⁻ z, ENNReal.ofReal (‖z r‖ ^ 2) ∂(P n : Measure (ℕ → ℂ)) ≤ M r) :
    IsTightMeasureSet (Set.range fun n => (P n : Measure (ℕ → ℂ))) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hε
  simp only [zero_add] at hδε
  let w (r : ℕ) : ℝ≥0 := δ * (2⁻¹ : ℝ≥0) ^ (r + 5)
  have hw r : 0 < w r := by dsimp [w]; positivity
  let K : Set (ℕ → ℂ) := Set.pi Set.univ fun r =>
    Metric.closedBall 0 (Real.sqrt (((1 + M r) / w r : ℝ≥0) : ℝ))
  refine ⟨K, isCompact_univ_pi (fun _ => isCompact_closedBall _ _), ?_⟩
  rintro _ ⟨n, rfl⟩
  have hK : Kᶜ = ⋃ r, {z : ℕ → ℂ |
      Real.sqrt (((1 + M r) / w r : ℝ≥0) : ℝ) < ‖z r‖} := by
    ext z
    simp [K, Metric.mem_closedBall, dist_zero_right]
  have hcast r : (w r : ℝ≥0∞) = (δ : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ (r + 5) := by
    simp [w, ENNReal.inv_pow]
  calc
    (P n : Measure (ℕ → ℂ)) Kᶜ ≤ ∑' r, (w r : ℝ≥0∞) := by
      rw [hK]
      exact (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun r =>
        coordinate_tail_le r (M r) (w r) (hw r) (hM n r))
    _ = (δ : ℝ≥0∞) * (1 / 16) := by
      simp_rw [hcast]
      rw [ENNReal.tsum_mul_left, tsum_moment_failure_weights]
    _ ≤ δ := by
      calc
        (δ : ℝ≥0∞) * (1 / 16) ≤ δ * 1 := by gcongr; norm_num
        _ = δ := mul_one _
    _ ≤ ε := hδε.le

/-- Prokhorov's theorem gives an actual probability measure on the countable
coordinate space and a strictly increasing convergent subsequence. -/
theorem exists_jointLaw_limit
    (P : ℕ → ProbabilityMeasure (ℕ → ℂ)) (M : ℕ → ℝ≥0)
    (hM : ∀ n r, ∫⁻ z, ENNReal.ofReal (‖z r‖ ^ 2) ∂(P n : Measure (ℕ → ℂ)) ≤ M r) :
    ∃ Q : ProbabilityMeasure (ℕ → ℂ), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (P ∘ φ) atTop (𝓝 Q) := by
  have ht := jointLaws_tight_of_second_moments P M hM
  have hc : IsCompact (closure (Set.range P)) := by
    apply isCompact_closure_of_isTightMeasureSet
    convert ht using 1
    ext μ
    simp
  obtain ⟨Q, _, φ, hφ, hlim⟩ := hc.tendsto_subseq
    (fun n => subset_closure (Set.mem_range_self n))
  exact ⟨Q, φ, hφ, hlim⟩

/-- Continuous identities among coordinates survive weak convergence.
This applies to addition, rational complex scalars, conjugation, and modulus. -/
theorem jointLaw_limit_ae_eq
    {P : ℕ → ProbabilityMeasure (ℕ → ℂ)} {Q : ProbabilityMeasure (ℕ → ℂ)}
    (hlim : Tendsto P atTop (𝓝 Q))
    (f g : (ℕ → ℂ) → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ n, f =ᵐ[(P n : Measure (ℕ → ℂ))] g) :
    f =ᵐ[(Q : Measure (ℕ → ℂ))] g := by
  have h := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim
    (isClosed_eq hf hg).isOpen_compl
  have hz n : (P n : Measure (ℕ → ℂ)) {z | f z ≠ g z} = 0 := ae_iff.mp (hfg n)
  change (Q : Measure (ℕ → ℂ)) {z | f z ≠ g z} ≤
    liminf (fun n => (P n : Measure (ℕ → ℂ)) {z | f z ≠ g z}) atTop at h
  simp_rw [hz, liminf_const] at h
  exact ae_iff.mpr (le_antisymm h bot_le)

/-- A uniform bound for a nonnegative continuous observable passes to the
weak limit, even when the observable is unbounded. -/
theorem jointLaw_limit_integral_le
    {P : ℕ → ProbabilityMeasure (ℕ → ℂ)} {Q : ProbabilityMeasure (ℕ → ℂ)}
    (hlim : Tendsto P atTop (𝓝 Q))
    (f : (ℕ → ℂ) → ℝ) (hf : Continuous f) (hpos : ∀ z, 0 ≤ f z)
    (M : ℝ≥0∞) (hM : ∀ n, ∫⁻ z, ENNReal.ofReal (f z) ∂(P n : Measure (ℕ → ℂ)) ≤ M) :
    ∫⁻ z, ENNReal.ofReal (f z) ∂(Q : Measure (ℕ → ℂ)) ≤ M := by
  have h := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure hf hpos
    (fun _ hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG)
  apply h.trans
  calc
    liminf (fun n => ∫⁻ z, ENNReal.ofReal (f z) ∂(P n : Measure (ℕ → ℂ))) atTop ≤
        liminf (fun _ : ℕ => M) atTop := liminf_le_liminf (Eventually.of_forall hM)
    _ = M := liminf_const M

/-- In particular, every coordinate second- or fourth-moment bound used in
the paper is preserved by the limiting law. -/
theorem jointLaw_limit_coordinate_moment_le
    {P : ℕ → ProbabilityMeasure (ℕ → ℂ)} {Q : ProbabilityMeasure (ℕ → ℂ)}
    (hlim : Tendsto P atTop (𝓝 Q)) (r p : ℕ) (M : ℝ≥0)
    (hM : ∀ n, ∫⁻ z, ENNReal.ofReal (‖z r‖ ^ p) ∂(P n : Measure (ℕ → ℂ)) ≤ M) :
    ∫⁻ z, ENNReal.ofReal (‖z r‖ ^ p) ∂(Q : Measure (ℕ → ℂ)) ≤ M :=
  jointLaw_limit_integral_le hlim _ ((continuous_apply r).norm.pow p)
    (fun z => pow_nonneg (norm_nonneg (z r)) p) M hM

/-- The limiting coordinate functions really are elements of `L²(Q)`, as
required before taking their closed linear span. -/
theorem jointLaw_limit_coordinate_memLp
    {P : ℕ → ProbabilityMeasure (ℕ → ℂ)} {Q : ProbabilityMeasure (ℕ → ℂ)}
    (hlim : Tendsto P atTop (𝓝 Q)) (r : ℕ) (M : ℝ≥0)
    (hM : ∀ n, ∫⁻ z, ENNReal.ofReal (‖z r‖ ^ 2) ∂(P n : Measure (ℕ → ℂ)) ≤ M) :
    MemLp (fun z => z r) 2 (Q : Measure (ℕ → ℂ)) := by
  apply (memLp_two_iff_integrable_sq_norm (measurable_pi_apply r).aestronglyMeasurable).mpr
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((measurable_pi_apply r).norm.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun z => sq_nonneg ‖z r‖)).mp
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top
    (jointLaw_limit_coordinate_moment_le hlim r 2 M hM)

/-- An independently identified coordinate marginal remains that marginal in
the joint weak limit. This is the step used for the auxiliary Gaussian seed. -/
theorem jointLaw_limit_marginal
    {P : ℕ → ProbabilityMeasure (ℕ → ℂ)} {Q : ProbabilityMeasure (ℕ → ℂ)}
    (hlim : Tendsto P atTop (𝓝 Q)) (r : ℕ) (γ : ProbabilityMeasure ℂ)
    (hγ : Tendsto (fun n => (P n).map (measurable_pi_apply r).aemeasurable) atTop (𝓝 γ)) :
    Q.map (measurable_pi_apply r).aemeasurable = γ :=
  tendsto_nhds_unique
    (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous P Q hlim (continuous_apply r)) hγ

end OperatorPhaseRetrieval

end
