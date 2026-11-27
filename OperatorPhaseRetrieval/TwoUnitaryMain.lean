import OperatorPhaseRetrieval.TwoUnitaryBaire
import OperatorPhaseRetrieval.TwoUnitaryRecovery
import OperatorPhaseRetrieval.TwoUnitarySpatial

/-! Phase retrieval by the identity and one arbitrarily close unitary on complex L²(ℝ). -/
noncomputable section

open MeasureTheory Filter
open scoped Topology ComplexConjugate

namespace OperatorPhaseRetrieval.TwoUnitary

/-- Theorem A on the circle with its normalized Haar measure. -/
theorem circle_phase_retrieval (ε : ℝ) (hε : 0 < ε) :
    ∃ V : Op, IsUnitary V ∧ ‖V - 1‖ < ε ∧ ∀ f g : H,
      ModEq f g → ModEq (V f) (V g) → ∃ c : Circle, g = c • f := by
  obtain ⟨V,hV,hnear,happrox⟩ := simultaneous_readouts ε hε
  refine ⟨V,hV,hnear,fun f g hfg hVfg => phase_of_gram (fun i j => ?_)⟩
  obtain ⟨N,z,hbound,hentry⟩ := happrox i j
  let A (k : ℕ) := readout V (N k) (z k)
  have ht := tendsto_quad_of_entries A i j hbound hentry
  have he (k : ℕ) : quad (A k) f = quad (A k) g := readout_quad_eq V _ _ hfg hVfg
  exact tendsto_nhds_unique (ht f) ((ht g).congr (fun k => (he k).symm))

end OperatorPhaseRetrieval.TwoUnitary

namespace OperatorPhaseRetrieval

/-- Theorem A on `L²(ℝ)`. -/
theorem two_unitaries_near_identity (ε : ℝ) (hε : 0 < ε) :
    ∃ U : L2 (volume : Measure ℝ) →L[ℂ] L2 (volume : Measure ℝ),
      (Isometry U ∧ Function.Surjective U) ∧ ‖U - 1‖ < ε ∧
      ∀ f g, ModEq f g → ModEq (U f) (U g) → ∃ c : Circle, g = c • f := by
  obtain ⟨V,hV,hnear,hpr⟩ := TwoUnitary.circle_phase_retrieval ε hε
  exact TwoUnitary.transfer_to_line ε V hV hnear hpr

end OperatorPhaseRetrieval
