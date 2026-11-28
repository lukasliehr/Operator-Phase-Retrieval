module

public import OperatorPhaseRetrieval.ProbabilitySpatial
public import OperatorPhaseRetrieval.WeightedL2
public import Mathlib.MeasureTheory.Measure.WithDensityFinite

@[expose] public section

noncomputable section

/-! Existence of spatial unitaries for atomless sigma-finite standard Borel measures. -/
open Filter ProbabilityTheory MeasureTheory Set
open scoped InnerProductSpace CStarAlgebra ComplexConjugate Topology NNReal ENNReal
namespace OperatorPhaseRetrieval
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [StandardBorelSpace Y]

theorem sigmaFinite_spatial_unitary (μ : Measure X) [SigmaFinite μ] [NeZero μ] [NullSingletonClass μ] :
    ∃ W : L2 uniformUnit ≃ₗᵢ[ℂ] L2 μ, ∀ f g, ModEq (W f) (W g) ↔ ModEq f g := by
  let : NullSingletonClass μ.toFinite :=
    ⟨fun x => toFinite_absolutelyContinuous μ (measure_singleton x)⟩
  obtain ⟨A, hA⟩ := equivalent_measures_unitary (μ := μ) μ.toFinite
    (absolutelyContinuous_toFinite μ) (toFinite_absolutelyContinuous μ)
  obtain ⟨B, hB⟩ := probability_spatial_unitary μ.toFinite
  exact ⟨B.trans A, fun f g => (hA (B f) (B g)).trans (hB f g)⟩

/-- The transfer lemma: existence, including normalization, null sets, and density weights. -/
theorem exists_spatial_unitary (μ : Measure X) (ν : Measure Y)
    [SigmaFinite μ] [SigmaFinite ν] [NeZero μ] [NeZero ν] [NullSingletonClass μ] [NullSingletonClass ν] :
    ∃ W : L2 μ ≃ₗᵢ[ℂ] L2 ν, ∀ f g, ModEq (W f) (W g) ↔ ModEq f g := by
  obtain ⟨A,hA⟩ := sigmaFinite_spatial_unitary μ
  obtain ⟨B,hB⟩ := sigmaFinite_spatial_unitary ν
  refine ⟨A.symm.trans B, fun f g => ?_⟩
  have ha : ModEq (A.symm f) (A.symm g) ↔ ModEq f g := by
    simpa using (hA (A.symm f) (A.symm g)).symm
  exact (hB (A.symm f) (A.symm g)).trans ha

end OperatorPhaseRetrieval

end
