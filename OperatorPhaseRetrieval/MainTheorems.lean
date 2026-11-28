module

public import OperatorPhaseRetrieval.Formulations
public import OperatorPhaseRetrieval.TwoUnitaryMain

@[expose] public section

/-!
# The main theorems

Theorems A, B and C in the formulation of `Challenge.lean`, with the definitions of that file
written out. Theorem A is obtained from the two measurements on `L²(ℝ)` in `TwoUnitaryMain.lean`,
and Theorems B and C from the proof assembly in `SeparableAtomless.lean`.
-/

noncomputable section

open MeasureTheory TopologicalSpace

namespace OperatorPhaseRetrieval

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Two measurements are transported along a unitary which preserves moduli. -/
theorem transfer_two_unitaries {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    (W : L2 ν ≃ₗᵢ[ℂ] L2 μ) (hW : ∀ f g, ModEq (W f) (W g) ↔ ModEq f g) (ε : ℝ)
    (V : L2 μ →L[ℂ] L2 μ) (hV : Isometry V ∧ Function.Surjective V) (hne : ‖V - 1‖ < ε)
    (hpr : ∀ f g : L2 μ, ModEq f g → ModEq (V f) (V g) → ∃ c : Circle, g = c • f) :
    ∃ U : L2 ν →L[ℂ] L2 ν, (Isometry U ∧ Function.Surjective U) ∧ ‖U - 1‖ < ε ∧
      ∀ f g, ModEq f g → ModEq (U f) (U g) → ∃ c : Circle, g = c • f := by
  let U := transport W V
  have hnorm (x : L2 ν) : ‖(U - 1) x‖ = ‖(V - 1) (W x)‖ := by
    rw [← W.norm_map ((U - 1) x)]
    simp [U, map_sub, sub_apply, transport_apply]
  refine ⟨U, ⟨W.symm.isometry.comp (hV.1.comp W.isometry),
    W.symm.surjective.comp (hV.2.comp W.surjective)⟩, ?_, ?_⟩
  · apply lt_of_le_of_lt _ hne
    refine (U - 1).opNorm_le_bound (norm_nonneg _) (fun x => ?_)
    rw [hnorm, ← W.norm_map x]
    exact (V - 1).le_opNorm _
  · intro f g hfg hU
    have hm := (hW (U f) (U g)).2 hU
    change ModEq (W (transport W V f)) (W (transport W V g)) at hm
    simp only [map_transport] at hm
    obtain ⟨c, hc⟩ := hpr (W f) (W g) ((hW f g).2 hfg) hm
    refine ⟨c, W.injective ?_⟩
    change W g = W ((c : ℂ) • f)
    rwa [W.map_smul]

/-- The identity and a nearby unitary on every separable non-atomic `L²` space. -/
theorem two_unitaries_of_separable_atomless (μ : Measure X) [SeparableSpace (L2 μ)]
    (hμ : AtomlessMeasure μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : L2 μ →L[ℂ] L2 μ, (Isometry U ∧ Function.Surjective U) ∧ ‖U - 1‖ < ε ∧
      ∀ f g, ModEq f g → ModEq (U f) (U g) → ∃ c : Circle, g = c • f := by
  rcases subsingleton_or_nontrivial (L2 μ) with hzero | hnonzero
  · let : Subsingleton (L2 μ) := hzero
    refine ⟨1, ⟨AddMonoidHomClass.isometry_of_norm (1 : L2 μ →L[ℂ] L2 μ) (fun _ => rfl),
      fun f => ⟨f, rfl⟩⟩, by simpa using hε, fun f g _ _ => ⟨1, Subsingleton.elim _ _⟩⟩
  · let : Nontrivial (L2 μ) := hnonzero
    obtain ⟨W, hW⟩ := exists_separable_atomless_spatial_unitary μ hμ
    obtain ⟨V, hV, hne, hpr⟩ := two_unitaries_near_identity ε hε
    exact transfer_two_unitaries W.symm
      (fun f g => by simpa using (hW (W.symm f) (W.symm g)).symm) ε V hV hne hpr

/-- Theorem A in the formulation of `Challenge.lean`. -/
theorem uniqueness_from_two_measurements (μ : Measure X) [SeparableSpace (L2 μ)]
    (hμ : AtomlessMeasure μ) :
    ∀ ε > 0, ∃ U : L2 μ →L[ℂ] L2 μ, (Isometry U ∧ Function.Surjective U) ∧ ‖U - 1‖ < ε ∧
      ∀ ψ φ : L2 μ, (∀ j, modulusLp (![1, U] j ψ) = modulusLp (![1, U] j φ)) →
        ∃ θ : ℝ, φ = Complex.exp (θ * Complex.I) • ψ := by
  intro ε hε
  obtain ⟨U, hU, hne, hpr⟩ := two_unitaries_of_separable_atomless μ hμ ε hε
  refine ⟨U, hU, hne, fun ψ φ h => ?_⟩
  obtain ⟨c, hc⟩ := hpr ψ φ (modEq_of_modulusLp_eq (h 0)) (modEq_of_modulusLp_eq (h 1))
  obtain ⟨θ, hθ⟩ := exists_real_phase c.norm_coe
  refine ⟨θ, ?_⟩
  rw [← hθ]
  exact hc

/-- Theorem B in the formulation of `Challenge.lean`. -/
theorem stability_from_five_measurements (μ : Measure X) [SeparableSpace (L2 μ)]
    (hμ : AtomlessMeasure μ) :
    ∃ U : Fin 5 → L2 μ →L[ℂ] L2 μ, (∀ j, Isometry (U j) ∧ Function.Surjective (U j)) ∧
      U 0 = 1 ∧ ∃ C > 0, ∀ ψ φ : L2 μ, ⨅ θ : ℝ, ‖ψ - Complex.exp (θ * Complex.I) • φ‖ ≤
        C * ⨆ j, ‖modulusLp (U j ψ) - modulusLp (U j φ)‖ := by
  obtain ⟨V, hV0, hV⟩ := fiveUnitaryStability_of_separable_atomless μ hμ
  refine ⟨fun j => (V j).toContinuousLinearEquiv.toContinuousLinearMap,
    fun j => ⟨(V j).isometry, (V j).surjective⟩, ?_, 2 ^ 100, by positivity, fun ψ φ => ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    show V 0 x = x
    rw [hV0]
    rfl
  · exact StableUnitaryFamily.iInf_le (fun f g => (hV f g).1) ψ φ

/-- Theorem C in the formulation of `Challenge.lean`. -/
theorem uniqueness_from_three_measurements (μ : Measure X) [SeparableSpace (L2 μ)]
    (hμ : AtomlessMeasure μ) :
    ∃ P : L2 μ →L[ℂ] L2 μ, (P * P = P ∧ star P = P) ∧
      ∀ η : Fin 3 → Circle, Function.Injective η →
        let U := fun j => 1 + ((η j : ℂ) - 1) • P
        (∀ j, Isometry (U j) ∧ Function.Surjective (U j)) ∧
        ∀ ψ φ : L2 μ, (∀ j, modulusLp (U j ψ) = modulusLp (U j φ)) →
          ∃ θ : ℝ, φ = Complex.exp (θ * Complex.I) • ψ := by
  obtain ⟨P, hP, h⟩ := phase_retrieval_of_separable_atomless μ hμ
  refine ⟨P, hP, fun η hη => ?_⟩
  obtain ⟨hU, hPR⟩ := h (fun j => (η j : ℂ)) (fun j => (η j).norm_coe)
    (Circle.coe_injective.comp hη)
  refine ⟨fun j => (hU j).isometry_surjective, fun ψ φ hψφ => ?_⟩
  obtain ⟨ω, hω, hφ⟩ := hPR ψ φ fun j => modEq_of_modulusLp_eq (hψφ j)
  obtain ⟨θ, rfl⟩ := exists_real_phase hω
  exact ⟨θ, hφ⟩

end OperatorPhaseRetrieval

end
