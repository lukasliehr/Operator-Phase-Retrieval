import OperatorPhaseRetrieval.SphereInvariance
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.MeasureTheory.Measure.Haar.Unique

noncomputable section

open MeasureTheory Set Metric TopologicalSpace
open scoped ENNReal NNReal

namespace OperatorPhaseRetrieval

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- The unitary group with the operator-norm topology inherited from endomorphisms. -/
abbrev HaarUnitary := unitary (E →L[ℂ] E)

theorem unitaryOperator_norm_le (u : HaarUnitary E) : ‖(u : E →L[ℂ] E)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [Unitary.norm_map u, one_mul]

instance haarUnitary_compactSpace : CompactSpace (HaarUnitary E) := by
  apply isCompact_iff_compactSpace.mp
  apply isCompact_iff_isClosed_bounded.mpr
  refine ⟨isClosed_unitary, isBounded_iff_forall_norm_le.mpr ⟨1, ?_⟩⟩
  intro u hu
  exact unitaryOperator_norm_le E ⟨u, hu⟩

instance haarUnitary_measurableSpace : MeasurableSpace (HaarUnitary E) := borel _

instance haarUnitary_borelSpace : BorelSpace (HaarUnitary E) := ⟨rfl⟩

def haarUnitaryProbability : ProbabilityMeasure (HaarUnitary E) :=
  ⟨Measure.haarMeasure (⟨⟨univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts (HaarUnitary E)),
    ⟨Measure.haarMeasure_self⟩⟩

instance haarUnitaryProbability_isHaarMeasure :
    (haarUnitaryProbability E : Measure (HaarUnitary E)).IsHaarMeasure := by
  dsimp [haarUnitaryProbability]
  infer_instance

instance haarUnitaryProbability_isMulRightInvariant :
    (haarUnitaryProbability E : Measure (HaarUnitary E)).IsMulRightInvariant := by
  constructor
  intro u
  let := Measure.isProbabilityMeasure_map
    (μ := (haarUnitaryProbability E : Measure (HaarUnitary E)))
    (measurable_mul_const u).aemeasurable
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

def haarUnitaryRealEquiv (u : HaarUnitary E) : E ≃ₗᵢ[ℝ] E :=
  { toLinearEquiv := (Unitary.linearIsometryEquiv u).toLinearEquiv.restrictScalars ℝ
    norm_map' := Unitary.norm_map u }

def unitarySphereAction (u : HaarUnitary E) (x : sphere (0 : E) 1) : sphere (0 : E) 1 :=
  ⟨(u : E →L[ℂ] E) x, by simpa only [mem_sphere, dist_zero_right, Unitary.norm_map] using x.property⟩

theorem unitarySphereAction_mul (u v : HaarUnitary E) (x : sphere (0 : E) 1) :
    unitarySphereAction E (u * v) x = unitarySphereAction E u (unitarySphereAction E v x) := rfl

theorem unitarySphereAction_continuous : Continuous (Function.uncurry (unitarySphereAction E)) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_fst).clm_apply
    (continuous_subtype_val.comp continuous_snd)

theorem exists_unitary_map_unit_vector (x y : E) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∃ u : HaarUnitary E, (u : E →L[ℂ] E) x = y := by
  let ex := LinearIsometryEquiv.toSpanUnitSingleton (𝕜 := ℂ) x hx
  let ey := LinearIsometryEquiv.toSpanUnitSingleton (𝕜 := ℂ) y hy
  let L : (ℂ ∙ x) →ₗᵢ[ℂ] E := (ℂ ∙ y).subtypeₗᵢ.comp (ex.symm.trans ey).toLinearIsometry
  let u := L.extend.toLinearIsometryEquiv rfl
  refine ⟨Unitary.linearIsometryEquiv.symm u, ?_⟩
  change L.extend x = y
  have hsub : (⟨x, Submodule.mem_span_singleton_self x⟩ : ℂ ∙ x) = ex 1 := by
    ext
    simp [ex]
  have hL : L ⟨x, Submodule.mem_span_singleton_self x⟩ = y := by
    rw [hsub]
    change ((ey (ex.symm (ex 1))) : E) = y
    rw [ex.symm_apply_apply]
    simp [ey]
  exact (L.extend_apply ⟨x, Submodule.mem_span_singleton_self x⟩).trans hL

theorem unitarySphereAction_transitive (x y : sphere (0 : E) 1) :
    ∃ u : HaarUnitary E, unitarySphereAction E u x = y := by
  obtain ⟨u, hu⟩ := exists_unitary_map_unit_vector E x y (by simp) (by simp)
  exact ⟨u, Subtype.ext hu⟩

variable [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

local instance : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E

theorem unitarySphereAction_measurePreserving (u : HaarUnitary E) :
    MeasurePreserving (unitarySphereAction E u) (uniformSphere E : Measure _) (uniformSphere E : Measure _) :=
  uniformSphere_measurePreserving (haarUnitaryRealEquiv E u)

end OperatorPhaseRetrieval

end
