module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-!
# Informational completeness for pure quantum states

Theorems A and B are the two main results of the paper "Informational completeness for pure
quantum states: minimality and stability" by L. Liehr, D. Omer, B. Pineau and M. A. Taylor.
Theorem C is a further result. The proofs are in `Solution.lean`.
-/

open MeasureTheory TopologicalSpace Complex

namespace InformationalCompleteness

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The Hilbert space `L²(X,μ)` of wave functions. -/
local notation "L²(" μ ")" => Lp ℂ 2 μ

/-- The bounded linear operators on `L²(X,μ)`. -/
abbrev Operator (μ : Measure X) := L²(μ) →L[ℂ] L²(μ)

/-- The unit circle in the complex plane. -/
local notation "𝕋" => Circle

/-- Every measurable set of positive measure splits into two measurable sets of positive measure. -/
def NonAtomic (μ : Measure X) : Prop :=
  ∀ s, MeasurableSet s → 0 < μ s → ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ t ∧ 0 < μ (s \ t)

/-- The modulus `|ψ|` of `ψ ∈ L²(X,μ)`, a real-valued function in `L²(X,μ)`. -/
noncomputable def modulus (ψ : L²(μ)) : Lp ℝ 2 μ :=
  MemLp.toLp (fun x => ‖ψ x‖) (Lp.memLp ψ).norm

local notation "|" ψ "|" => modulus ψ

/-- A unitary operator is a surjective linear isometry. -/
def IsUnitary (U : Operator μ) : Prop := Isometry U ∧ Function.Surjective U

/-- An orthogonal projection `P` satisfies `P² = P = P*`. -/
def IsOrthogonalProjection (P : Operator μ) : Prop := P * P = P ∧ star P = P

/-- `U₁, …, Uₘ` are informationally complete with respect to pure states. -/
def InformationallyComplete {m : ℕ} (U : Fin m → Operator μ) : Prop :=
  ∀ ψ φ : L²(μ), (∀ j, |U j ψ| = |U j φ|) → ∃ θ : ℝ, φ = exp (θ * I) • ψ

/-- The distance `d(ψ,φ) = min_θ ‖ψ - e^{iθ}φ‖` of `ψ` and `φ` modulo global phase. -/
noncomputable def d (ψ φ : L²(μ)) : ℝ := ⨅ θ : ℝ, ‖ψ - exp (θ * I) • φ‖

/-- `U₁, …, Uₘ` determine pure states stably. -/
def DeterminePureStatesStably {m : ℕ} (U : Fin m → Operator μ) : Prop :=
  ∃ C > 0, ∀ ψ φ : L²(μ), d ψ φ ≤ C * ⨆ j, ‖|U j ψ| - |U j φ|‖

/-- Theorem A: the identity and a unitary operator close to it are informationally complete. -/
theorem uniqueness_from_two_measurements (hμ : NonAtomic μ) [SeparableSpace L²(μ)] :
    ∀ ε > 0, ∃ U : Operator μ, IsUnitary U ∧ ‖U - 1‖ < ε ∧ InformationallyComplete ![1, U] := by
  sorry

/-- Theorem B: five unitary operators, the first one the identity, determine pure states stably. -/
theorem stability_from_five_measurements (hμ : NonAtomic μ) [SeparableSpace L²(μ)] :
    ∃ U : Fin 5 → Operator μ, (∀ j, IsUnitary (U j)) ∧ U 0 = 1 ∧ DeterminePureStatesStably U := by
  sorry

/-- Theorem C: three unitary operators built from one projection are informationally complete. -/
theorem uniqueness_from_three_measurements (hμ : NonAtomic μ) [SeparableSpace L²(μ)] :
    ∃ P : Operator μ, IsOrthogonalProjection P ∧ ∀ η : Fin 3 → 𝕋, Function.Injective η →
      let U := fun j => 1 + ((η j : ℂ) - 1) • P
      (∀ j, IsUnitary (U j)) ∧ InformationallyComplete U := by
  sorry

end InformationalCompleteness
