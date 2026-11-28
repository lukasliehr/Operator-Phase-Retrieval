module

public import OperatorPhaseRetrieval.SeparableSupport
public import OperatorPhaseRetrieval.FiveUnitaryStability

@[expose] public section

/-! Both main theorems for arbitrary atomless measures with separable L². -/

noncomputable section

open MeasureTheory Set Filter TopologicalSpace

namespace OperatorPhaseRetrieval

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem separable_sigmaFinite_spatial_unitary [SigmaFinite μ] [NeZero μ]
    [SeparableSpace (L2 μ)] (hμ : AtomlessMeasure μ) :
    ∃ W : L2 uniformUnit ≃ₗᵢ[ℂ] L2 μ,
      ∀ f g, ModEq (W f) (W g) ↔ ModEq f g := by
  obtain ⟨A, hA⟩ := equivalent_measures_unitary (μ := μ) μ.toFinite
    (absolutelyContinuous_toFinite μ) (toFinite_absolutelyContinuous μ)
  let : SeparableSpace (L2 μ.toFinite) := A.isometry.isEmbedding.separableSpace
  obtain ⟨B, hB⟩ := separable_probability_spatial_unitary
    (hμ.of_equivalent (toFinite_absolutelyContinuous μ) (absolutelyContinuous_toFinite μ))
  exact ⟨B.trans A, fun f g => (hA (B f) (B g)).trans (hB f g)⟩

/-- The common spatial reduction for a nontrivial separable atomless L² space. -/
theorem exists_separable_atomless_spatial_unitary
    [SeparableSpace (L2 μ)] [Nontrivial (L2 μ)] (hμ : AtomlessMeasure μ) :
    ∃ W : RealL2 ≃ₗᵢ[ℂ] L2 μ,
      ∀ f g, ModEq (W f) (W g) ↔ ModEq f g := by
  obtain ⟨s, hs, hfin, A, hA⟩ := exists_sigmaFinite_L2_model (μ := μ)
  let : SigmaFinite (μ.restrict s) := hfin
  let : SeparableSpace (L2 (μ.restrict s)) := A.isometry.isEmbedding.separableSpace
  let : Nontrivial (L2 (μ.restrict s)) := A.toEquiv.nontrivial
  have hn : μ.restrict s ≠ 0 := by
    intro hz
    have hsub : Subsingleton (L2 (μ.restrict s)) := ⟨fun f g => by
      apply Lp.ext
      simp [hz, Filter.EventuallyEq]⟩
    exact not_subsingleton (L2 (μ.restrict s)) hsub
  let : NeZero (μ.restrict s) := ⟨hn⟩
  obtain ⟨B, hB⟩ := separable_sigmaFinite_spatial_unitary (μ.restrict s) (hμ.restrict hs)
  obtain ⟨C, hC⟩ := sigmaFinite_spatial_unitary (volume : Measure ℝ)
  let D := B.trans A
  refine ⟨C.symm.trans D, fun f g => ?_⟩
  have he : ModEq (C.symm f) (C.symm g) ↔ ModEq f g := by
    simpa using (hC (C.symm f) (C.symm g)).symm
  exact ((hA _ _).trans (hB _ _)).trans he

/-- Theorem C for every non-atomic measure space with separable `L²`. -/
theorem phase_retrieval_of_separable_atomless [SeparableSpace (L2 μ)]
    (hμ : AtomlessMeasure μ) : ProjectionWorks (@ModEq X _ μ) := by
  rcases subsingleton_or_nontrivial (L2 μ) with hzero | hnonzero
  · let : Subsingleton (L2 μ) := hzero
    have hp : IsOrthogonalProjection (0 : L2 μ →L[ℂ] L2 μ) := by
      constructor <;> simp
    refine ⟨0, hp, fun η hη _ => ⟨fun j => phaseFamily_unitary _ hp (hη j), ?_⟩⟩
    intro f g _
    exact ⟨1, norm_one, Subsingleton.elim _ _⟩
  · let : Nontrivial (L2 μ) := hnonzero
    obtain ⟨W, hW⟩ := exists_separable_atomless_spatial_unitary μ hμ
    apply transfer_projectionWorks W.symm (hS := main)
    intro f g
    simpa using (hW (W.symm f) (W.symm g)).symm

/-- Theorem B, preserving both explicit constants and the identity first operator. -/
theorem fiveUnitaryStability_of_separable_atomless [SeparableSpace (L2 μ)]
    (hμ : AtomlessMeasure μ) : FiveUnitaryStability μ := by
  rcases subsingleton_or_nontrivial (L2 μ) with hzero | hnonzero
  · let : Subsingleton (L2 μ) := hzero
    apply fiveUnitaryStability_of_family (fun _ => LinearIsometryEquiv.refl ℂ (L2 μ))
    intro f g
    have hd : phaseDistance f g = 0 :=
      (phaseDistance_eq_zero_iff f g).mpr ⟨1, norm_one, Subsingleton.elim _ _⟩
    rw [hd, mul_zero]
    exact measurementDistance_nonneg _ _ _
  · let : Nontrivial (L2 μ) := hnonzero
    obtain ⟨W, hW⟩ := exists_separable_atomless_spatial_unitary μ hμ
    obtain ⟨U, _, hU⟩ := fiveUnitaryStability_real
    exact fiveUnitaryStability_of_family (transportUnitaryFamily W U)
      (stableUnitaryFamily_transport W hW (fun f g => (hU f g).1))

end OperatorPhaseRetrieval

end
