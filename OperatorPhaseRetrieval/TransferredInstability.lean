import OperatorPhaseRetrieval.Main
import OperatorPhaseRetrieval.MagnitudeDistance

noncomputable section

/-! Quantitative instability on the original L2 space, for the same projection
that gives phase retrieval. -/
open Filter ProbabilityTheory Set MeasureTheory
open scoped InnerProductSpace CStarAlgebra ComplexConjugate Topology NNReal ENNReal
namespace OperatorPhaseRetrieval

/-- Uniform continuity of recovery modulo a constant phase, on the unit sphere. -/
def L2UniformPhaseRecovery {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    (T : ι → L2 μ →L[ℂ] L2 μ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ f g : L2 μ, ‖f‖ = 1 → ‖g‖ = 1 →
      (∀ j, ‖magnitude (T j f)-magnitude (T j g)‖ < δ) →
      ∃ ω : ℂ, IsPhase ω ∧ ‖f-ω • g‖ < ε

theorem uniformRecovery_of_transport {X Y ι : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    (W : L2 ν ≃ₗᵢ[ℂ] SumL2 (L2 μ))
    (hW : ∀ f g, PairModEq (W f) (W g) ↔ ModEq f g)
    (P : SumL2 (L2 μ) →L[ℂ] SumL2 (L2 μ)) (η : ι → ℂ)
    (h : L2UniformPhaseRecovery (fun j => phaseFamily (transport W P) (η j))) :
    UniformPhaseRecovery (fun j => phaseFamily P (η j)) := by
  intro ε hε
  obtain ⟨δ,hδ,hr⟩ := h ε hε
  refine ⟨δ,hδ,fun x y hx hy hd => ?_⟩
  have hdata : ∀ j,
      ‖magnitude (phaseFamily (transport W P) (η j) (W.symm x))-
        magnitude (phaseFamily (transport W P) (η j) (W.symm y))‖ < δ := by
    intro j
    rw [← pair_spatial_magnitudeDistance W hW]
    simpa only [map_phaseFamily_transport,W.apply_symm_apply] using hd j
  obtain ⟨ω,hω,hclose⟩ := hr (W.symm x) (W.symm y)
    (by simpa using hx) (by simpa using hy) hdata
  refine ⟨ω,hω,?_⟩
  simpa only [← W.symm.map_smul,← W.symm.map_sub,W.symm.norm_map] using hclose

theorem transported_no_uniform_recovery {X Y ι : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    (W : L2 ν ≃ₗᵢ[ℂ] SumL2 (L2 μ))
    (hW : ∀ f g, PairModEq (W f) (W g) ↔ ModEq f g)
    (D : L2 μ →L[ℂ] L2 μ) (b : HilbertBasis ℕ ℂ (L2 μ))
    {w : ℕ → ℝ} (hw : Summable w) (hD : IsSelfAdjoint D)
    (hcomm : Commute (diagonalSmoothing b w) D)
    (hsq : diagonalSmoothing b w * diagonalSmoothing b w + D*D=1)
    (η : ι → ℂ) (hη : ∀ j, IsPhase (η j)) :
    ¬ L2UniformPhaseRecovery (fun j =>
      phaseFamily (transport W (blockProjection (diagonalSmoothing b w) D)) (η j)) := by
  intro h
  exact diagonal_no_uniform_phase_recovery D b hw hD hcomm hsq η hη
    (uniformRecovery_of_transport W hW _ η h)


end OperatorPhaseRetrieval

end
