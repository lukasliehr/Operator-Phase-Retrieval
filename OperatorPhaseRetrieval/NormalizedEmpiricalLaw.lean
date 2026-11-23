import OperatorPhaseRetrieval.EmpiricalLaw
import OperatorPhaseRetrieval.NormalizedEmpirical

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace OperatorPhaseRetrieval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]

def scaledProbability (ν : ProbabilityMeasure E) (b : ℝ) : ProbabilityMeasure E :=
  ν.map ((measurable_id.const_smul b).aemeasurable)

/-- Weak convergence of empirical laws is preserved by a convergent common
rescaling when their first absolute moments remain bounded. -/
theorem empiricalLaw_rescale_tendsto (z : ℕ → E) (ν : ProbabilityMeasure E)
    (a : ℕ → ℝ) (b R : ℝ) (ha : Tendsto a atTop (𝓝 b))
    (hR : Tendsto (fun n => empiricalAverage (fun x => ‖x‖) z (n+1)) atTop (𝓝 R))
    (hν : Tendsto (empiricalLaw z) atTop (𝓝 ν)) :
    Tendsto (fun n => empiricalLaw (fun i => a n • z i) n) atTop (𝓝 (scaledProbability ν b)) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro h hb hh
  obtain ⟨K, hK⟩ := hh
  let g : BoundedContinuousFunction E ℝ :=
    { toFun := fun x => h (b • x)
      continuous_toFun := hK.continuous.comp (continuous_id.const_smul b)
      map_bounded' := by obtain ⟨C, hC⟩ := hb; exact ⟨C, fun x y => hC _ _⟩ }
  have hg := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν) g
  have hint : Tendsto (fun n => empiricalAverage (fun x => h (b • x)) z (n+1))
      atTop (𝓝 (∫ x, h (b • x) ∂(ν : Measure E))) := by
    simp_rw [empiricalLaw_integral _ _ _ g.continuous.measurable] at hg
    simpa [empiricalAverage, g] using hg
  have hv := empiricalAverage_rescale_tendsto z h hK (fun n => n+1) a b R _ ha hR hint
  have hi : (∫ x, h x ∂(scaledProbability ν b : Measure E)) =
      ∫ x, h (b • x) ∂(ν : Measure E) := by
    exact integral_map (measurable_id.const_smul b).aemeasurable hK.continuous.measurable.aestronglyMeasurable
  rw [hi]
  simpa only [empiricalLaw_integral _ _ _ hK.continuous.measurable, empiricalAverage,
    smul_eq_mul] using hv

/-- The full weak law for empirical distributions of normalized iid samples. -/
theorem normalizedEmpiricalLaw_strongLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] [SecondCountableTopology E]
    (Z : ℕ → Ω → E) (hZm : ∀ i, Measurable (Z i)) (hZ : MemLp (Z 0) 2 P)
    (hindep : Pairwise (fun i j => IndepFun (Z i) (Z j) P))
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P)
    (ν : ProbabilityMeasure E) (hlaw : P.map (Z 0) = (ν : Measure E))
    (q : ℝ) (hq : 0 < q) (hqmean : ∫ ω, ‖Z 0 ω‖ ^ 2 ∂P = q) :
    ∀ᵐ ω ∂P, Tendsto (fun n => empiricalLaw
      (fun i => (Real.sqrt (empiricalAverage (fun y => ‖y‖ ^ 2)
        (fun j => Z j ω) (n+1)))⁻¹ • Z i ω) n)
      atTop (𝓝 (scaledProbability ν (Real.sqrt q)⁻¹)) := by
  have hs := strong_law_ae (fun i ω => ‖Z i ω‖ ^ 2) (hZ.integrable_norm_pow (by norm_num))
    (fun i j hij => (hindep hij).comp (measurable_norm.pow_const 2) (measurable_norm.pow_const 2))
    (fun i => (hident i).comp (measurable_norm.pow_const 2))
  have hn := strong_law_ae (fun i ω => ‖Z i ω‖) ((hZ.integrable (by norm_num)).norm)
    (fun i j hij => (hindep hij).comp measurable_norm measurable_norm)
    (fun i => (hident i).comp measurable_norm)
  rw [hqmean] at hs
  filter_upwards [empiricalLaw_strongLaw P Z hZm hindep hident ν hlaw, hs, hn] with ω hw hs hn
  apply empiricalLaw_rescale_tendsto (fun i => Z i ω) ν
    (fun n => (Real.sqrt (empiricalAverage (fun y => ‖y‖ ^ 2) (fun j => Z j ω) (n+1)))⁻¹)
    ((Real.sqrt q)⁻¹) (∫ ω, ‖Z 0 ω‖ ∂P)
  · exact (Real.continuous_sqrt.tendsto q |>.comp
      (hs.comp (tendsto_add_atTop_nat 1))).inv₀ (Real.sqrt_pos.mpr hq).ne'
  · exact hn.comp (tendsto_add_atTop_nat 1)
  · exact hw

end OperatorPhaseRetrieval

end
