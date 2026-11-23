import OperatorPhaseRetrieval.SeparableAtomless
import Mathlib.Analysis.Complex.Circle

/-!
# The main theorems as stated in the paper

`three_unitaries` and `five_unitary_stability` are Theorems 1.1 and 1.3 in the formulation of
`Showcase.lean`, with the definitions of that file written out. They follow from
`phase_retrieval_of_separable_atomless` and `fiveUnitaryStability_of_separable_atomless`.
-/

noncomputable section

open MeasureTheory TopologicalSpace

namespace OperatorPhaseRetrieval

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The modulus is the class of the pointwise modulus. -/
theorem magnitude_eq_toLp (f : L2 μ) :
    magnitude f = MemLp.toLp (fun x => ‖f x‖) (Lp.memLp f).norm := by
  apply Lp.ext
  filter_upwards [magnitude_coeFn f, (Lp.memLp f).norm.coeFn_toLp] with x h₁ h₂
  rw [h₁, h₂]

/-- A unitary operator is a surjective isometry. -/
theorem IsUnitary.isometry_surjective {U : L2 μ →L[ℂ] L2 μ} (hU : IsUnitary U) :
    Isometry U ∧ Function.Surjective U :=
  ⟨AddMonoidHomClass.isometry_of_norm U (unitary_norm U hU),
    fun f => ⟨star U f, congrArg (fun T : L2 μ →L[ℂ] L2 μ => T f) hU.2⟩⟩

/-- The distance modulo a constant phase is an infimum over the unit circle. -/
theorem phaseDistance_eq_iInf (f g : L2 μ) :
    phaseDistance f g = ⨅ ω : Circle, ‖f - ω • g‖ := by
  unfold phaseDistance iInf
  congr 1
  ext r
  constructor
  · rintro ⟨ω, hω, rfl⟩
    exact ⟨⟨ω, mem_sphere_zero_iff_norm.2 hω⟩, rfl⟩
  · rintro ⟨ω, rfl⟩
    exact ⟨ω, ω.norm_coe, rfl⟩

/-- The measurement distance is the largest of the component distances. -/
theorem measurementDistance_eq_iSup {ι : Type*} [Fintype ι] [Nonempty ι]
    (U : ι → L2 μ ≃ₗᵢ[ℂ] L2 μ) (f g : L2 μ) :
    measurementDistance U f g = ⨆ j, ‖magnitude (U j f) - magnitude (U j g)‖ := by
  have hb : BddAbove (Set.range fun j => ‖magnitude (U j f) - magnitude (U j g)‖) :=
    (Set.finite_range _).bddAbove
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (Real.iSup_nonneg fun j => norm_nonneg _)).mpr
    exact fun j => le_ciSup hb j
  · exact ciSup_le fun j => norm_le_pi_norm (fun k => magnitude (U k f) - magnitude (U k g)) j

/-- The stability estimate with the constant `2¹⁰⁰`, as an inequality between an infimum and a
maximum. -/
theorem StableUnitaryFamily.iInf_le {V : Fin 5 → L2 μ ≃ₗᵢ[ℂ] L2 μ}
    (hV : StableUnitaryFamily stabilityConstant V) (f g : L2 μ) :
    ⨅ ω : Circle, ‖f - ω • g‖ ≤ 2 ^ 100 * ⨆ j,
      ‖MemLp.toLp (fun x => ‖V j f x‖) (Lp.memLp (V j f)).norm -
        MemLp.toLp (fun x => ‖V j g x‖) (Lp.memLp (V j g)).norm‖ := by
  have h := hV f g
  rw [phaseDistance_eq_iInf, measurementDistance_eq_iSup] at h
  simp only [magnitude_eq_toLp] at h
  unfold stabilityConstant at h
  linarith

/-- Theorem 1.1 in the formulation of `Showcase.lean`. -/
theorem three_unitaries (μ : Measure X) [SeparableSpace (L2 μ)] (hμ : AtomlessMeasure μ) :
    ∃ P : L2 μ →L[ℂ] L2 μ, (P * P = P ∧ star P = P) ∧
      ∀ η : Fin 3 → Circle, Function.Injective η →
        let U := fun j => 1 + ((η j : ℂ) - 1) • P
        (∀ j, Isometry (U j) ∧ Function.Surjective (U j)) ∧
        ∀ f g : L2 μ,
          (∀ j, MemLp.toLp (fun x => ‖U j f x‖) (Lp.memLp (U j f)).norm =
            MemLp.toLp (fun x => ‖U j g x‖) (Lp.memLp (U j g)).norm) →
          ∃ c : Circle, f = c • g := by
  obtain ⟨P, hP, h⟩ := phase_retrieval_of_separable_atomless μ hμ
  refine ⟨P, hP, fun η hη => ?_⟩
  obtain ⟨hU, hPR⟩ := h (fun j => (η j : ℂ)) (fun j => (η j).norm_coe)
    (Circle.coe_injective.comp hη)
  refine ⟨fun j => (hU j).isometry_surjective, fun f g hfg => ?_⟩
  obtain ⟨ω, hω, rfl⟩ := hPR f g fun j => (MemLp.toLp_eq_toLp_iff _ _).mp (hfg j)
  have hs : ‖star ω‖ = 1 := (norm_star ω).trans hω
  refine ⟨⟨star ω, mem_sphere_zero_iff_norm.2 hs⟩, ?_⟩
  show f = star ω • ω • f
  rw [smul_smul, mul_comm, phase_mul_conj hω, one_smul]

/-- Theorem 1.3 in the formulation of `Showcase.lean`. -/
theorem five_unitary_stability (μ : Measure X) [SeparableSpace (L2 μ)]
    (hμ : AtomlessMeasure μ) :
    ∃ U : Fin 5 → L2 μ →L[ℂ] L2 μ, (∀ j, Isometry (U j) ∧ Function.Surjective (U j)) ∧
      ∃ C > 0, ∀ f g : L2 μ, ⨅ ω : Circle, ‖f - ω • g‖ ≤ C * ⨆ j,
        ‖MemLp.toLp (fun x => ‖U j f x‖) (Lp.memLp (U j f)).norm -
          MemLp.toLp (fun x => ‖U j g x‖) (Lp.memLp (U j g)).norm‖ := by
  obtain ⟨V, -, hV⟩ := fiveUnitaryStability_of_separable_atomless μ hμ
  refine ⟨fun j => (V j).toContinuousLinearEquiv.toContinuousLinearMap,
    fun j => ⟨(V j).isometry, (V j).surjective⟩, 2 ^ 100, by positivity, fun f g => ?_⟩
  exact StableUnitaryFamily.iInf_le (fun f g => (hV f g).1) f g

end OperatorPhaseRetrieval

end
