module

public import OperatorPhaseRetrieval.FiniteProbabilityL2
public import Mathlib.Probability.StrongLaw
public import Mathlib.MeasureTheory.Measure.Portmanteau

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped Topology

namespace OperatorPhaseRetrieval

variable {E : Type*} [MeasurableSpace E]

/-- Empirical probability law of the first `n+1` samples. -/
def empiricalLaw (z : ℕ → E) (n : ℕ) : ProbabilityMeasure E :=
  ⟨(finiteProbability (Fin (n+1))).map (fun i : Fin (n+1) => z i), inferInstance⟩

theorem empiricalLaw_integral (z : ℕ → E) (n : ℕ) (h : E → ℝ) (hm : Measurable h) :
    ∫ x, h x ∂(empiricalLaw z n : Measure E) =
      ((n+1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (n+1), h (z i) := by
  change ∫ x, h x ∂((finiteProbability (Fin (n+1))).map _) = _
  rw [integral_map (measurable_of_countable _).aemeasurable hm.aestronglyMeasurable,
    finiteProbability_integral]
  simp only [Fintype.card_fin, smul_eq_mul]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i => h (z i)) (n+1)

theorem empiricalLaw_real_apply (z : ℕ → E) (n : ℕ) (s : Set E) (hs : MeasurableSet s) :
    (empiricalLaw z n : Measure E).real s =
      ((n+1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (n+1), s.indicator (fun _ => (1 : ℝ)) (z i) := by
  rw [← integral_indicator_one hs]
  exact empiricalLaw_integral z n _ (measurable_const.indicator hs)

theorem empiricalLaw_congr {z w : ℕ → E} (n : ℕ)
    (h : ∀ i < n+1, z i = w i) : empiricalLaw z n = empiricalLaw w n := by
  apply Subtype.ext
  change (finiteProbability (Fin (n+1))).map (fun i : Fin (n+1) => z i) =
    (finiteProbability (Fin (n+1))).map (fun i : Fin (n+1) => w i)
  congr 1
  funext i
  exact h i i.isLt

theorem empiricalLaw_continuous [TopologicalSpace E] [BorelSpace E] (n : ℕ) :
    Continuous (fun z : ℕ → E => empiricalLaw z n) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  intro f
  simp_rw [empiricalLaw_integral _ _ _ f.continuous.measurable]
  exact continuous_const.mul (continuous_finsetSum _
    (fun i _ => f.continuous.comp (continuous_apply i)))

/-- Almost-sure weak convergence of iid empirical laws on a second-countable
space. The proof applies the strong law simultaneously on a countable π-system
of neighborhoods and then uses the portmanteau convergence criterion. -/
theorem empiricalLaw_strongLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    [TopologicalSpace E] [SecondCountableTopology E] [OpensMeasurableSpace E]
    (Z : ℕ → Ω → E) (hZ : ∀ i, Measurable (Z i))
    (hindep : Pairwise (fun i j => IndepFun (Z i) (Z j) P))
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P)
    (ν : ProbabilityMeasure E) (hlaw : P.map (Z 0) = (ν : Measure E)) :
    ∀ᵐ ω ∂P, Tendsto (empiricalLaw (fun i => Z i ω)) atTop (𝓝 ν) := by
  classical
  obtain ⟨b, hb⟩ := exists_seq_basis E
  let B (t : Finset ℕ) : Set E := ⋂ i ∈ t, b i
  have hBopen (t : Finset ℕ) : IsOpen (B t) :=
    isOpen_biInter_finset (fun i _ => hb.isOpen ⟨i, rfl⟩)
  have hpi : IsPiSystem (Set.range B) := by
    rintro s ⟨t, rfl⟩ u ⟨v, rfl⟩ _
    refine ⟨t ∪ v, ?_⟩
    ext x
    simp only [B, mem_inter_iff, mem_iInter, Finset.mem_union]
    constructor
    · intro hx
      exact ⟨fun i hi => hx i (Or.inl hi), fun i hi => hx i (Or.inr hi)⟩
    · rintro ⟨ht, hv⟩ i (hi | hi)
      · exact ht i hi
      · exact hv i hi
  have hsmall : ∀ u : Set E, IsOpen u → ∀ x ∈ u,
      ∃ s ∈ Set.range B, s ∈ 𝓝 x ∧ s ⊆ u := by
    intro u hu x hx
    obtain ⟨s, ⟨i, rfl⟩, hxi, hsu⟩ := hb.exists_subset_of_mem_open hx hu
    refine ⟨b i, ⟨{i}, by simp [B]⟩, (hb.isOpen ⟨i, rfl⟩).mem_nhds hxi, hsu⟩
  have hconv (t : Finset ℕ) : ∀ᵐ ω ∂P,
      Tendsto (fun n => (empiricalLaw (fun i => Z i ω) n : Measure E).real (B t))
        atTop (𝓝 ((ν : Measure E).real (B t))) := by
    let f : E → ℝ := (B t).indicator (fun _ => 1)
    have hm : Measurable f := measurable_const.indicator (hBopen t).measurableSet
    have hi : Integrable (fun ω => f (Z 0 ω)) P := by
      apply Integrable.of_bound (hm.comp (hZ 0)).aestronglyMeasurable 1
      exact Filter.Eventually.of_forall fun ω => by
        simp only [f]
        by_cases hx : Z 0 ω ∈ B t <;> simp [hx]
    have h := strong_law_ae (fun i ω => f (Z i ω)) hi
      (fun i j hij => (hindep hij).comp hm hm) (fun i => (hident i).comp hm)
    have hint : ∫ ω, f (Z 0 ω) ∂P = (ν : Measure E).real (B t) := by
      rw [← integral_map (hZ 0).aemeasurable hm.aestronglyMeasurable, hlaw]
      exact integral_indicator_one (hBopen t).measurableSet
    rw [hint] at h
    filter_upwards [h] with ω hω
    simpa only [empiricalLaw_real_apply _ _ _ (hBopen t).measurableSet,
      smul_eq_mul, Function.comp_def, f] using hω.comp (tendsto_add_atTop_nat 1)
  filter_upwards [ae_all_iff.mpr hconv] with ω hω
  apply hpi.tendsto_probabilityMeasure_of_tendsto_of_mem
    (fun s hs => by obtain ⟨t, rfl⟩ := hs; exact (hBopen t).measurableSet) hsmall
  rintro s ⟨t, rfl⟩
  apply NNReal.tendsto_coe.mp
  simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn] using hω t

end OperatorPhaseRetrieval

end
