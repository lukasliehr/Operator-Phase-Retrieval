import OperatorPhaseRetrieval.SeparableAtomless
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Formulations of the main notions

Lemmas which translate the notions of the library into the formulations used in
`Showcase.lean`: the modulus as an element of real `L²`, unitary operators as surjective
isometries, global phases `exp (θ * I)` and the distance modulo a global phase.
-/

noncomputable section

open MeasureTheory TopologicalSpace

namespace OperatorPhaseRetrieval

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The modulus of an `L²` function as an element of real `L²`, defined as in `Showcase.lean`. -/
def modulusLp (f : L2 μ) : Lp ℝ 2 μ :=
  MemLp.toLp (fun x => ‖f x‖) (Lp.memLp f).norm

theorem magnitude_eq_modulusLp (f : L2 μ) : magnitude f = modulusLp f := by
  apply Lp.ext
  filter_upwards [magnitude_coeFn f, (Lp.memLp f).norm.coeFn_toLp] with x h₁ h₂
  rw [h₁, modulusLp, h₂]

/-- Equal moduli in `L²` mean equal moduli almost everywhere. -/
theorem modEq_of_modulusLp_eq {f g : L2 μ} (h : modulusLp f = modulusLp g) : ModEq f g :=
  (MemLp.toLp_eq_toLp_iff _ _).mp h

/-- A unitary operator is a surjective isometry. -/
theorem IsUnitary.isometry_surjective {U : L2 μ →L[ℂ] L2 μ} (hU : IsUnitary U) :
    Isometry U ∧ Function.Surjective U :=
  ⟨AddMonoidHomClass.isometry_of_norm U (unitary_norm U hU),
    fun f => ⟨star U f, congrArg (fun T : L2 μ →L[ℂ] L2 μ => T f) hU.2⟩⟩

/-- Every unimodular complex number is of the form `exp (θ * I)` with `θ` real. -/
theorem exists_real_phase {ω : ℂ} (hω : IsPhase ω) :
    ∃ θ : ℝ, ω = Complex.exp (θ * Complex.I) := by
  refine ⟨Complex.arg ω, ?_⟩
  have h := Complex.norm_mul_exp_arg_mul_I ω
  rw [show ‖ω‖ = 1 from hω, Complex.ofReal_one, one_mul] at h
  exact h.symm

/-- The distance modulo a global phase is an infimum over real phases. -/
theorem phaseDistance_eq_iInf (f g : L2 μ) :
    phaseDistance f g = ⨅ θ : ℝ, ‖f - Complex.exp (θ * Complex.I) • g‖ := by
  unfold phaseDistance iInf
  congr 1
  ext r
  constructor
  · rintro ⟨ω, hω, rfl⟩
    obtain ⟨θ, rfl⟩ := exists_real_phase hω
    exact ⟨θ, rfl⟩
  · rintro ⟨θ, rfl⟩
    exact ⟨Complex.exp (θ * Complex.I), Complex.norm_exp_ofReal_mul_I θ, rfl⟩

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

/-- The stability estimate with the constant `2¹⁰⁰`, as an inequality between an infimum over
global phases and a maximum over the measurements. -/
theorem StableUnitaryFamily.iInf_le {V : Fin 5 → L2 μ ≃ₗᵢ[ℂ] L2 μ}
    (hV : StableUnitaryFamily stabilityConstant V) (f g : L2 μ) :
    ⨅ θ : ℝ, ‖f - Complex.exp (θ * Complex.I) • g‖ ≤
      2 ^ 100 * ⨆ j, ‖modulusLp (V j f) - modulusLp (V j g)‖ := by
  have h := hV f g
  rw [phaseDistance_eq_iInf, measurementDistance_eq_iSup] at h
  simp only [magnitude_eq_modulusLp] at h
  unfold stabilityConstant at h
  linarith

end OperatorPhaseRetrieval

end
