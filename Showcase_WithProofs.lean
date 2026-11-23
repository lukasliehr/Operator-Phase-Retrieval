import OperatorPhaseRetrieval

/-!
# Stable recovery from magnitudes of unitary operators

Theorems 1.1 and 1.3 of the paper by L. Liehr, D. Omer, B. Pineau and M. A. Taylor.
The definitions and statements are those of `Showcase.lean`, here with proofs.
-/

open MeasureTheory TopologicalSpace

namespace WrightsConjecture

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The complex Hilbert space `L²(X,μ)`. -/
local notation "L²(" μ ")" => Lp ℂ 2 μ

/-- The unit circle in the complex plane. -/
local notation "𝕋" => Circle

/-- Every measurable set of positive measure splits into two measurable sets of positive measure. -/
def NonAtomic (μ : Measure X) : Prop :=
  ∀ s, MeasurableSet s → 0 < μ s → ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ t ∧ 0 < μ (s \ t)

/-- The modulus `|f|` of `f ∈ L²(X,μ)`, a real-valued function in `L²(X,μ)`. -/
noncomputable def modulus (f : L²(μ)) : Lp ℝ 2 μ :=
  MemLp.toLp (fun x => ‖f x‖) (Lp.memLp f).norm

local notation "|" f "|" => modulus f

/-- A bounded linear operator `P` on `L²(X,μ)` is an orthogonal projection if `P² = P = P*`. -/
def IsOrthogonalProjection (P : L²(μ) →L[ℂ] L²(μ)) : Prop := P * P = P ∧ star P = P

/-- A bounded linear operator `U` on `L²(X,μ)` is unitary if it is a surjective isometry. -/
def IsUnitary (U : L²(μ) →L[ℂ] L²(μ)) : Prop := Isometry U ∧ Function.Surjective U

/-- The operators `U j` do phase retrieval. -/
def DoesPhaseRetrieval {J : Type*} (U : J → L²(μ) →L[ℂ] L²(μ)) : Prop :=
  ∀ f g : L²(μ), (∀ j, |U j f| = |U j g|) → ∃ c : 𝕋, f = c • g

/-- Theorem 1.1: three unitary operators do phase retrieval. -/
theorem three_unitaries (hμ : NonAtomic μ) [SeparableSpace L²(μ)] :
    ∃ P : L²(μ) →L[ℂ] L²(μ), IsOrthogonalProjection P ∧
      ∀ η : Fin 3 → 𝕋, Function.Injective η →
        let U := fun j => 1 + ((η j : ℂ) - 1) • P
        (∀ j, IsUnitary (U j)) ∧ DoesPhaseRetrieval U := by
  exact OperatorPhaseRetrieval.three_unitaries μ hμ

/-- Theorem 1.3: five unitary operators do stable phase retrieval. -/
theorem five_unitary_stability (hμ : NonAtomic μ) [SeparableSpace L²(μ)] :
    ∃ U : Fin 5 → L²(μ) →L[ℂ] L²(μ), (∀ j, IsUnitary (U j)) ∧ ∃ C > 0, ∀ f g : L²(μ),
      ⨅ ω : 𝕋, ‖f - ω • g‖ ≤ C * ⨆ j, ‖|U j f| - |U j g|‖ := by
  exact OperatorPhaseRetrieval.five_unitary_stability μ hμ

end WrightsConjecture
