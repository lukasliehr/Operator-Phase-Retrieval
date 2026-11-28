module

public import OperatorPhaseRetrieval.EmpiricalLaw

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OperatorPhaseRetrieval

variable {E : Type*} [MeasurableSpace E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The probability distribution giving equal mass to all entries of a finite vector. -/
def finiteEmpiricalLaw (z : ι → E) : ProbabilityMeasure E :=
  letI : MeasurableSpace ι := ⊤
  ⟨(finiteProbability ι).map z, inferInstance⟩

theorem finiteEmpiricalLaw_integral (z : ι → E) (h : E → ℝ) (hm : Measurable h) :
    ∫ x, h x ∂(finiteEmpiricalLaw z : Measure E) =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, h (z i) := by
  let : MeasurableSpace ι := ⊤
  change ∫ x, h x ∂((finiteProbability ι).map z) = _
  rw [integral_map (measurable_of_countable _).aemeasurable hm.aestronglyMeasurable,
    finiteProbability_integral, smul_eq_mul]

theorem finiteEmpiricalLaw_continuous [TopologicalSpace E] [BorelSpace E] :
    Continuous (finiteEmpiricalLaw : (ι → E) → ProbabilityMeasure E) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  intro f
  simp_rw [finiteEmpiricalLaw_integral _ _ f.continuous.measurable]
  exact continuous_const.mul (continuous_finsetSum _
    (fun i _ => f.continuous.comp (continuous_apply i)))

theorem empiricalLaw_eq_finiteEmpiricalLaw
    (z : ℕ → E) (n : ℕ) :
    empiricalLaw z n = finiteEmpiricalLaw (fun i : Fin (n+1) => z i) := by
  rfl

end OperatorPhaseRetrieval

end
