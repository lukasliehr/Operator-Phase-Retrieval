module

public import OperatorPhaseRetrieval.MathlibImports

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace OperatorPhaseRetrieval

/-- A transitive measurable action identifies any invariant probability measure
with the law of a fixed point acted on by a right-invariant random group element. -/
theorem map_orbit_eq_of_invariant_probability {G S : Type*}
    [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableSpace S]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (ν : Measure S) [IsProbabilityMeasure ν]
    (act : G → S → S) (hact : Measurable (Function.uncurry act))
    (hmul : ∀ g h y, act (g * h) y = act g (act h y))
    (hpres : ∀ g, MeasurePreserving (act g) ν ν)
    (x : S) (htrans : ∀ y, ∃ g, act g x = y) :
    Measure.map (fun g => act g x) μ = ν := by
  have hm (y : S) : Measurable (fun g => act g y) :=
    hact.comp (measurable_id.prodMk measurable_const)
  apply Measure.ext
  intro s hs
  let q : S → ℝ≥0∞ := s.indicator (fun _ => 1)
  have hq : Measurable q := measurable_const.indicator hs
  have horbit (y : S) : (∫⁻ g, q (act g y) ∂μ) = ∫⁻ g, q (act g x) ∂μ := by
    obtain ⟨h, rfl⟩ := htrans y
    calc
      _ = ∫⁻ g, q (act (g * h) x) ∂μ := by simp only [hmul]
      _ = _ := (measurePreserving_mul_right μ h).lintegral_comp (hq.comp (hm x))
  have hfixed (g : G) : (∫⁻ y, q (act g y) ∂ν) = ν s := by
    rw [(hpres g).lintegral_comp hq]
    exact lintegral_indicator_one hs
  have hswap := lintegral_lintegral_swap
    (μ := μ) (ν := ν) (f := fun g y => q (act g y)) (hq.comp hact).aemeasurable
  have hint : (∫⁻ g, q (act g x) ∂μ) = ν s := by
    calc
      _ = ∫⁻ y, ∫⁻ g, q (act g y) ∂μ ∂ν := by simp only [horbit, lintegral_const, measure_univ, mul_one]
      _ = ∫⁻ g, ∫⁻ y, q (act g y) ∂ν ∂μ := hswap.symm
      _ = _ := by simp only [hfixed, lintegral_const, measure_univ, mul_one]
  rw [Measure.map_apply (hm x) hs]
  rw [← hint]
  change μ ((fun g => act g x) ⁻¹' s) =
    ∫⁻ g, ((fun g => act g x) ⁻¹' s).indicator (fun _ => 1) g ∂μ
  exact (lintegral_indicator_one ((hm x) hs)).symm

end OperatorPhaseRetrieval

end
