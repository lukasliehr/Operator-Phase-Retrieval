import OperatorPhaseRetrieval.StabilityReduction

/-! # Passing stability bounds to limits and dense subsets -/

noncomputable section

open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace OperatorPhaseRetrieval

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {ι : Type*} [Fintype ι]

theorem continuous_measurementDistance (U : ι → L2 μ ≃ₗᵢ[ℂ] L2 μ) :
    Continuous (fun p : L2 μ × L2 μ => measurementDistance U p.1 p.2) := by
  apply Continuous.norm
  apply continuous_pi
  intro j
  have hm : Continuous (magnitude (μ := μ)) :=
    lipschitzWith_one_norm.continuous_compLp (norm_zero : ‖(0 : ℂ)‖ = 0)
  exact (hm.comp ((U j).continuous.comp continuous_fst)).sub
    (hm.comp ((U j).continuous.comp continuous_snd))

/-- Extend a lower bound from any dense set of formal expressions. -/
theorem stableUnitaryFamily_of_dense {c : ℝ} (U : ι → L2 μ ≃ₗᵢ[ℂ] L2 μ)
    {S : Set (L2 μ)} (hS : Dense S)
    (hU : ∀ f ∈ S, ∀ g ∈ S, c * phaseDistance f g ≤ measurementDistance U f g) :
    StableUnitaryFamily c U := by
  have hc : IsClosed {p : L2 μ × L2 μ |
      c * phaseDistance p.1 p.2 ≤ measurementDistance U p.1 p.2} :=
    isClosed_le (continuous_const.mul (continuous_phaseDistance (H := L2 μ)))
      (continuous_measurementDistance U)
  have hd : Dense (S ×ˢ S) := hS.prod hS
  have hsub : S ×ˢ S ⊆ {p : L2 μ × L2 μ |
      c * phaseDistance p.1 p.2 ≤ measurementDistance U p.1 p.2} :=
    fun p hp => hU p.1 hp.1 p.2 hp.2
  intro f g
  exact hd.induction
    (P := fun p => c * phaseDistance p.1 p.2 ≤ measurementDistance U p.1 p.2)
    (fun _ hp => hsub hp) hc (f, g)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Phase distances converge when the squared norms and inner products converge,
even when the finite-dimensional Hilbert spaces vary with the index. -/
theorem phaseDistance_tendsto_of_norm_inner
    {J : Type*} {l : Filter J}
    (E : J → Type*) [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℂ (E n)]
    (f g : ∀ n, E n) (u v : H)
    (hf : Tendsto (fun n => ‖f n‖ ^ 2) l (𝓝 (‖u‖ ^ 2)))
    (hg : Tendsto (fun n => ‖g n‖ ^ 2) l (𝓝 (‖v‖ ^ 2)))
    (hi : Tendsto (fun n => ⟪f n, g n⟫_ℂ) l (𝓝 ⟪u, v⟫_ℂ)) :
    Tendsto (fun n => phaseDistance (f n) (g n)) l (𝓝 (phaseDistance u v)) := by
  simp_rw [phaseDistance_eq_sqrt]
  exact ((hf.add hg).sub (tendsto_const_nhds.mul hi.norm)).sqrt

/-- A measurable function with an atomless marginal forces singleton sets
in its source to be null. On a standard Borel probability space this is the
condition used by the spatial-unitary transfer theorem. -/
theorem nullSingletonClass_of_map {Y : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (f : X → Y) (hf : AEMeasurable f μ) [NullSingletonClass (μ.map f)] :
    NullSingletonClass μ := by
  constructor
  intro x
  apply le_antisymm _ bot_le
  calc
    μ {x} ≤ μ (f ⁻¹' {f x}) := measure_mono (by
      intro y hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact Set.mem_singleton _)
    _ = μ.map f {f x} := (Measure.map_apply_of_aemeasurable hf (measurableSet_singleton _)).symm
    _ = 0 := measure_singleton _

end OperatorPhaseRetrieval

end
