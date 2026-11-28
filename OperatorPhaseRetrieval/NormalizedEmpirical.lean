module

public import OperatorPhaseRetrieval.GaussianMoments
public import Mathlib.Probability.StrongLaw

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology NNReal

namespace OperatorPhaseRetrieval

/-- Empirical average over the first `n` coordinates. -/
def empiricalAverage {E F : Type*} [AddCommMonoid F] [Module ℝ F]
    (h : E → F) (z : ℕ → E) (n : ℕ) : F := (n : ℝ)⁻¹ • ∑ i ∈ range n, h (z i)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem empiricalAverage_rescale_bound (z : ℕ → E) (h : E → F)
    {K : ℝ≥0} (hh : LipschitzWith K h) (a b : ℝ) (n : ℕ) :
    ‖empiricalAverage (fun x => h (a • x)) z n -
      empiricalAverage (fun x => h (b • x)) z n‖ ≤
        K * |a - b| * empiricalAverage (fun x => ‖x‖) z n := by
  unfold empiricalAverage
  rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)⁻¹)]
  calc
    (n : ℝ)⁻¹ * ‖∑ i ∈ range n, (h (a • z i) - h (b • z i))‖ ≤
        (n : ℝ)⁻¹ * ∑ i ∈ range n, ‖h (a • z i) - h (b • z i)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (n : ℝ)⁻¹ * ∑ i ∈ range n, (K * |a - b| * ‖z i‖) := by
      gcongr with i hi
      have h' := hh.dist_le_mul (a • z i) (b • z i)
      simpa only [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs, mul_assoc] using h'
    _ = _ := by rw [← Finset.mul_sum]; simp only [smul_eq_mul]; ring

/-- Convergent rescaling does not change an empirical limit when the first
absolute moments remain bounded (here supplied by their convergence). -/
theorem empiricalAverage_rescale_tendsto (z : ℕ → E) (h : E → F)
    {K : ℝ≥0} (hh : LipschitzWith K h) (N : ℕ → ℕ) (a : ℕ → ℝ) (b R : ℝ) (v : F)
    (ha : Tendsto a atTop (𝓝 b))
    (hR : Tendsto (fun n => empiricalAverage (fun x => ‖x‖) z (N n)) atTop (𝓝 R))
    (hv : Tendsto (fun n => empiricalAverage (fun x => h (b • x)) z (N n)) atTop (𝓝 v)) :
    Tendsto (fun n => empiricalAverage (fun x => h (a n • x)) z (N n)) atTop (𝓝 v) := by
  have hz : Tendsto (fun n => (K : ℝ) * |a n - b| *
      empiricalAverage (fun x => ‖x‖) z (N n)) atTop (𝓝 0) := by
    convert (tendsto_const_nhds.mul (ha.sub tendsto_const_nhds).abs).mul hR using 1
    simp
  have hd : Tendsto (fun n =>
      ‖empiricalAverage (fun x => h (a n • x)) z (N n) -
        empiricalAverage (fun x => h (b • x)) z (N n)‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun n => empiricalAverage_rescale_bound z h hh (a n) b (N n)) hz
  have hdiff : Tendsto (fun n => empiricalAverage (fun x => h (a n • x)) z (N n) -
      empiricalAverage (fun x => h (b • x)) z (N n)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hd
  have hsum := hdiff.add hv
  simpa only [sub_add_cancel, zero_add] using hsum

/-- Strong law for a Lipschitz observable of iid vectors after normalization by
their empirical second moment. -/
theorem normalized_empirical_strongLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]
    (Z : ℕ → Ω → E) (hZ : MemLp (Z 0) 2 P)
    (hindep : Pairwise (fun i j => IndepFun (Z i) (Z j) P))
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P)
    (q : ℝ) (hq : 0 < q) (hqmean : ∫ ω, ‖Z 0 ω‖ ^ 2 ∂P = q)
    (h : E → F) (hm : Measurable h) {K : ℝ≥0} (hh : LipschitzWith K h)
    (hint : Integrable (fun ω => h ((Real.sqrt q)⁻¹ • Z 0 ω)) P) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n => empiricalAverage
        (fun x => h ((Real.sqrt (empiricalAverage (fun y => ‖y‖ ^ 2)
          (fun i => Z i ω) n))⁻¹ • x)) (fun i => Z i ω) n)
        atTop (𝓝 (∫ ω, h ((Real.sqrt q)⁻¹ • Z 0 ω) ∂P)) := by
  have hs := strong_law_ae (fun i ω => ‖Z i ω‖ ^ 2) (hZ.integrable_norm_pow (by norm_num))
    (fun i j hij => (hindep hij).comp (measurable_norm.pow_const 2) (measurable_norm.pow_const 2))
    (fun i => (hident i).comp (measurable_norm.pow_const 2))
  have hn := strong_law_ae (fun i ω => ‖Z i ω‖) ((hZ.integrable (by norm_num)).norm)
    (fun i j hij => (hindep hij).comp measurable_norm measurable_norm)
    (fun i => (hident i).comp measurable_norm)
  have hg : Measurable (fun x : E => h ((Real.sqrt q)⁻¹ • x)) :=
    hm.comp (measurable_const.smul measurable_id)
  have ht := strong_law_ae (fun i ω => h ((Real.sqrt q)⁻¹ • Z i ω)) hint
    (fun i j hij => (hindep hij).comp hg hg) (fun i => (hident i).comp hg)
  rw [hqmean] at hs
  filter_upwards [hs, hn, ht] with ω hs hn ht
  apply empiricalAverage_rescale_tendsto (fun i => Z i ω) h hh id
    (fun n => (Real.sqrt (empiricalAverage (fun y => ‖y‖ ^ 2) (fun i => Z i ω) n))⁻¹)
    ((Real.sqrt q)⁻¹) (∫ ω, ‖Z 0 ω‖ ∂P)
  · exact (Real.continuous_sqrt.tendsto q |>.comp hs).inv₀ (Real.sqrt_pos.mpr hq).ne'
  · exact hn
  · exact ht

end OperatorPhaseRetrieval

end
