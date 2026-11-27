import OperatorPhaseRetrieval.PhaseDistance
import OperatorPhaseRetrieval.MagnitudeDistance
import OperatorPhaseRetrieval.SpatialExistence

/-!
# Unitary stability estimates and their transport

These results prove the deterministic assembly steps of Theorem B.
`FiveUnitaryStability` states the existence of five unitaries with explicit stability constants.
-/

noncomputable section

open MeasureTheory

namespace OperatorPhaseRetrieval

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem magnitude_phase_smul (f : L2 μ) {ω : ℂ} (hω : IsPhase ω) :
    magnitude (ω • f) = magnitude f :=
  (magnitude_eq_of_modEq (modEq_smul f hω)).symm

theorem magnitudeDistance_le_phaseDistance (f g : L2 μ) :
    ‖magnitude f - magnitude g‖ ≤ phaseDistance f g := by
  obtain ⟨ω, hω, he, _⟩ := phaseDistance_attained f g
  rw [he, ← magnitude_phase_smul g hω]
  exact magnitude_sub_le f (ω • g)

variable {ι : Type*} [Fintype ι]

/-- The maximum of the component L² distances, expressed by Mathlib's finite Pi norm. -/
def measurementDistance (U : ι → L2 μ ≃ₗᵢ[ℂ] L2 μ) (f g : L2 μ) : ℝ :=
  ‖fun j => magnitude (U j f) - magnitude (U j g)‖

theorem measurementDistance_nonneg (U : ι → L2 μ ≃ₗᵢ[ℂ] L2 μ) (f g : L2 μ) :
    0 ≤ measurementDistance U f g := norm_nonneg _

/-- The measurement distance is at most the phase distance, for every finite family of unitaries. -/
theorem measurementDistance_le_phaseDistance (U : ι → L2 μ ≃ₗᵢ[ℂ] L2 μ) (f g : L2 μ) :
    measurementDistance U f g ≤ phaseDistance f g := by
  apply (pi_norm_le_iff_of_nonneg (phaseDistance_nonneg f g)).mpr
  intro j
  calc
    ‖magnitude (U j f) - magnitude (U j g)‖ ≤ phaseDistance (U j f) (U j g) :=
      magnitudeDistance_le_phaseDistance _ _
    _ = phaseDistance f g := phaseDistance_map (U j).toLinearIsometry f g

def StableUnitaryFamily (c : ℝ) (U : ι → L2 μ ≃ₗᵢ[ℂ] L2 μ) : Prop :=
  ∀ f g, c * phaseDistance f g ≤ measurementDistance U f g

theorem stableUnitaryFamily_phaseRetrieval {c : ℝ} (hc : 0 < c)
    {U : ι → L2 μ ≃ₗᵢ[ℂ] L2 μ} (hU : StableUnitaryFamily c U)
    (f g : L2 μ) (hm : ∀ j, ModEq (U j f) (U j g)) : PhaseRelated f g := by
  apply (phaseDistance_eq_zero_iff f g).mp
  have he : measurementDistance U f g = 0 := by
    unfold measurementDistance
    have hz : (fun j => magnitude (U j f) - magnitude (U j g)) = 0 := by
      funext j
      exact sub_eq_zero.mpr (magnitude_eq_of_modEq (hm j))
    rw [hz, norm_zero]
  have hl := hU f g
  rw [he] at hl
  nlinarith [phaseDistance_nonneg f g]

/-- Right composition with the inverse of one measurement makes that measurement the identity. -/
def normalizeUnitaryFamily (U : ι → L2 μ ≃ₗᵢ[ℂ] L2 μ) (j₀ : ι) :
    ι → L2 μ ≃ₗᵢ[ℂ] L2 μ := fun j => (U j₀).symm.trans (U j)

omit [Fintype ι] in
theorem normalizeUnitaryFamily_identity (U : ι → L2 μ ≃ₗᵢ[ℂ] L2 μ) (j₀ : ι) :
    normalizeUnitaryFamily U j₀ j₀ = LinearIsometryEquiv.refl ℂ (L2 μ) := by
  ext f : 1
  exact (U j₀).apply_symm_apply f

theorem stableUnitaryFamily_normalize {c : ℝ} {U : ι → L2 μ ≃ₗᵢ[ℂ] L2 μ}
    (hU : StableUnitaryFamily c U) (j₀ : ι) :
    StableUnitaryFamily c (normalizeUnitaryFamily U j₀) := by
  intro f g
  have h := hU ((U j₀).symm f) ((U j₀).symm g)
  have hp : phaseDistance ((U j₀).symm f) ((U j₀).symm g) = phaseDistance f g :=
    phaseDistance_map (U j₀).symm.toLinearIsometry f g
  rw [hp] at h
  exact h

variable {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}

def transportUnitaryFamily (W : L2 μ ≃ₗᵢ[ℂ] L2 ν) (U : ι → L2 μ ≃ₗᵢ[ℂ] L2 μ) :
    ι → L2 ν ≃ₗᵢ[ℂ] L2 ν := fun j => (W.symm.trans (U j)).trans W

theorem measurementDistance_transport (W : L2 μ ≃ₗᵢ[ℂ] L2 ν)
    (hW : ∀ f g, ModEq (W f) (W g) ↔ ModEq f g)
    (U : ι → L2 μ ≃ₗᵢ[ℂ] L2 μ) (f g : L2 ν) :
    measurementDistance (transportUnitaryFamily W U) f g =
      measurementDistance U (W.symm f) (W.symm g) := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (measurementDistance_nonneg U _ _)).mpr
    intro j
    change ‖magnitude (W (U j (W.symm f))) - magnitude (W (U j (W.symm g)))‖ ≤ _
    rw [spatial_magnitudeDistance W hW]
    exact norm_le_pi_norm (fun k => magnitude (U k (W.symm f)) - magnitude (U k (W.symm g))) j
  · apply (pi_norm_le_iff_of_nonneg (measurementDistance_nonneg _ _ _)).mpr
    intro j
    rw [← spatial_magnitudeDistance W hW]
    exact norm_le_pi_norm
      (fun k => magnitude (transportUnitaryFamily W U k f) -
        magnitude (transportUnitaryFamily W U k g)) j

theorem stableUnitaryFamily_transport (W : L2 μ ≃ₗᵢ[ℂ] L2 ν)
    (hW : ∀ f g, ModEq (W f) (W g) ↔ ModEq f g)
    {c : ℝ} {U : ι → L2 μ ≃ₗᵢ[ℂ] L2 μ} (hU : StableUnitaryFamily c U) :
    StableUnitaryFamily c (transportUnitaryFamily W U) := by
  intro f g
  rw [measurementDistance_transport W hW]
  have h := hU (W.symm f) (W.symm g)
  have hp : phaseDistance (W.symm f) (W.symm g) = phaseDistance f g :=
    phaseDistance_map W.symm.toLinearIsometry f g
  rw [hp] at h
  exact h

/-- The stability constant `2⁻¹⁰⁰`, written as a positive reciprocal power. -/
def stabilityConstant : ℝ := 1 / (2 : ℝ) ^ 100

theorem stabilityConstant_pos : 0 < stabilityConstant := by
  unfold stabilityConstant
  positivity

/-- Theorem B as a proposition, with five surjective unitaries and first measurement identity.
The existence of such a family is proved in `SeparableAtomless.lean`. -/
def FiveUnitaryStability (μ : Measure X) : Prop :=
  ∃ U : Fin 5 → L2 μ ≃ₗᵢ[ℂ] L2 μ,
    U 0 = LinearIsometryEquiv.refl ℂ (L2 μ) ∧
    ∀ f g, stabilityConstant * phaseDistance f g ≤ measurementDistance U f g ∧
      measurementDistance U f g ≤ phaseDistance f g

/-- Deterministic final assembly: normalize the first measurement and prove the upper bound. -/
theorem fiveUnitaryStability_of_family (U : Fin 5 → L2 μ ≃ₗᵢ[ℂ] L2 μ)
    (hU : StableUnitaryFamily stabilityConstant U) : FiveUnitaryStability μ := by
  refine ⟨normalizeUnitaryFamily U 0, normalizeUnitaryFamily_identity U 0, fun f g => ?_⟩
  exact ⟨stableUnitaryFamily_normalize hU 0 f g, measurementDistance_le_phaseDistance _ f g⟩

/-- The transfer of Theorem B between standard Borel spaces. -/
theorem fiveUnitaryStability_transfer [StandardBorelSpace X] [StandardBorelSpace Y]
    [SigmaFinite μ] [SigmaFinite ν] [NeZero μ] [NeZero ν]
    [NullSingletonClass μ] [NullSingletonClass ν]
    (h : FiveUnitaryStability μ) : FiveUnitaryStability ν := by
  obtain ⟨U, _, hU⟩ := h
  obtain ⟨W, hW⟩ := exists_spatial_unitary μ ν
  exact fiveUnitaryStability_of_family (transportUnitaryFamily W U)
    (stableUnitaryFamily_transport W hW (fun f g => (hU f g).1))

end OperatorPhaseRetrieval

end
