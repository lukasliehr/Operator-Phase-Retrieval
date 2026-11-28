module

public import OperatorPhaseRetrieval.HaarUnitary
public import OperatorPhaseRetrieval.HomogeneousProbability

@[expose] public section

noncomputable section

open MeasureTheory Set Metric

namespace OperatorPhaseRetrieval

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

local instance : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E

/-- A Haar unitary sends any fixed unit vector to the canonical uniform sphere law. -/
theorem haarUnitary_sphere_law (x : sphere (0 : E) 1) :
    Measure.map (fun u => unitarySphereAction E u x) (haarUnitaryProbability E : Measure _) =
      (uniformSphere E : Measure _) := by
  apply map_orbit_eq_of_invariant_probability
    (haarUnitaryProbability E : Measure _) (uniformSphere E : Measure _)
    (unitarySphereAction E) (unitarySphereAction_continuous E).measurable
    (unitarySphereAction_mul E) (unitarySphereAction_measurePreserving E) x
  exact fun y => unitarySphereAction_transitive E x y

theorem haarUnitary_sphere_measurePreserving (x : sphere (0 : E) 1) :
    MeasurePreserving (fun u => unitarySphereAction E u x)
      (haarUnitaryProbability E : Measure _) (uniformSphere E : Measure _) :=
  ⟨(unitarySphereAction_continuous E).measurable.comp (measurable_id.prodMk measurable_const),
    haarUnitary_sphere_law E x⟩

end OperatorPhaseRetrieval

end
