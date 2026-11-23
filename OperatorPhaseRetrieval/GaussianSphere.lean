import OperatorPhaseRetrieval.HaarSphere
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.Normed.Module.Normalize

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric NormedSpace

namespace OperatorPhaseRetrieval

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

theorem stdGaussian_nullSingletonClass : NullSingletonClass (stdGaussian E) := by
  apply IsGaussian.nullSingletonClass
  intro x hx
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have h := variance_dual_stdGaussian (innerSL ℝ v)
  rw [hx, variance_dirac, innerSL_apply_norm] at h
  exact (pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)) h.symm

def sphereDirection (x0 : sphere (0 : E) 1) (x : E) : sphere (0 : E) 1 := by
  classical
  exact if hx : x = 0 then x0 else ⟨NormedSpace.normalize x, by
    simpa only [mem_sphere, dist_zero_right] using norm_normalize hx⟩

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem sphereDirection_measurable (x0 : sphere (0 : E) 1) : Measurable (sphereDirection x0) := by
  classical
  suffices hm : Measurable (fun x => ((sphereDirection x0 x : sphere (0 : E) 1) : E)) from
    hm.subtype_mk (h := fun x => (sphereDirection x0 x).property)
  have he : (fun x => ((sphereDirection x0 x : sphere (0 : E) 1) : E)) =
      fun x => if x = 0 then (x0 : E) else NormedSpace.normalize x := by
    funext x
    by_cases hx : x = 0 <;> simp [sphereDirection, hx]
  rw [he]
  exact measurable_const.ite (measurableSet_singleton 0)
    (measurable_norm.inv.smul measurable_id)

theorem sphereDirection_isometry_ae (x0 : sphere (0 : E) 1) (e : E ≃ₗᵢ[ℝ] E) :
    (fun x => sphereDirection x0 (e x)) =ᵐ[stdGaussian E]
      (fun x => unitSphereEquiv e (sphereDirection x0 x)) := by
  let := stdGaussian_nullSingletonClass (E := E)
  filter_upwards [(stdGaussian E).ae_ne (0 : E)] with x hx
  have hex : e x ≠ 0 := fun h => hx (e.injective (h.trans e.map_zero.symm))
  apply Subtype.ext
  simp only [sphereDirection, dif_neg hx, dif_neg hex]
  change NormedSpace.normalize (e x) = e (NormedSpace.normalize x)
  simp only [NormedSpace.normalize, map_smul, e.norm_map]

theorem gaussian_direction_invariant (x0 : sphere (0 : E) 1) (e : E ≃ₗᵢ[ℝ] E) :
    Measure.map (unitSphereEquiv e) ((stdGaussian E).map (sphereDirection x0)) =
      (stdGaussian E).map (sphereDirection x0) := by
  rw [Measure.map_map (unitSphereEquiv e).continuous.measurable (sphereDirection_measurable x0)]
  calc
    _ = (stdGaussian E).map ((sphereDirection x0) ∘ e) :=
      Measure.map_congr (sphereDirection_isometry_ae x0 e).symm
    _ = ((stdGaussian E).map e).map (sphereDirection x0) :=
      (Measure.map_map (sphereDirection_measurable x0) e.continuous.measurable).symm
    _ = _ := by rw [stdGaussian_map e]

end OperatorPhaseRetrieval

namespace OperatorPhaseRetrieval

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

local instance : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E

/-- Normalizing a standard real Gaussian vector in a complex Hilbert space
gives the canonical uniform sphere distribution. The arbitrary value at zero
has no effect on this law. -/
theorem gaussian_direction_uniform (x0 : sphere (0 : E) 1) :
    (stdGaussian E).map (sphereDirection x0) = (uniformSphere E : Measure _) := by
  let ν := (stdGaussian E).map (sphereDirection x0)
  let := Measure.isProbabilityMeasure_map (μ := stdGaussian E) (sphereDirection_measurable x0).aemeasurable
  have hpres (u : HaarUnitary E) : MeasurePreserving (unitarySphereAction E u) ν ν :=
    ⟨(unitarySphereAction_continuous E).measurable.comp (measurable_const.prodMk measurable_id),
      gaussian_direction_invariant x0 (haarUnitaryRealEquiv E u)⟩
  have h := map_orbit_eq_of_invariant_probability
    (haarUnitaryProbability E : Measure _) ν (unitarySphereAction E)
    (unitarySphereAction_continuous E).measurable (unitarySphereAction_mul E) hpres x0
    (fun y => unitarySphereAction_transitive E x0 y)
  rw [haarUnitary_sphere_law] at h
  exact h.symm

/-- A Haar unitary applied to a fixed unit vector has the law of a normalized
standard Gaussian. This is equality of the actual vector-valued pushforward laws. -/
theorem haarUnitary_unitVector_gaussian_law (f : E) (hf : ‖f‖ = 1) :
    (haarUnitaryProbability E : Measure (HaarUnitary E)).map
      (fun U : HaarUnitary E => (U : E →L[ℂ] E) f) =
        (stdGaussian E).map NormedSpace.normalize := by
  let x0 : sphere (0 : E) 1 := ⟨f, by simpa only [mem_sphere, dist_zero_right]⟩
  have hmap : ((haarUnitaryProbability E : Measure (HaarUnitary E)).map
      (fun U => unitarySphereAction E U x0)).map (Subtype.val : sphere (0 : E) 1 → E) =
      ((stdGaussian E).map (sphereDirection x0)).map Subtype.val := by
    rw [haarUnitary_sphere_law, gaussian_direction_uniform]
  have hm : Measurable (fun U : HaarUnitary E => unitarySphereAction E U x0) :=
    (unitarySphereAction_continuous E).measurable.comp (measurable_id.prodMk measurable_const)
  rw [Measure.map_map measurable_subtype_coe hm,
    Measure.map_map measurable_subtype_coe (sphereDirection_measurable x0)] at hmap
  change (haarUnitaryProbability E : Measure (HaarUnitary E)).map
      (fun U : HaarUnitary E => (U : E →L[ℂ] E) f) = _ at hmap
  refine hmap.trans (Measure.map_congr ?_)
  let := stdGaussian_nullSingletonClass (E := E)
  filter_upwards [(stdGaussian E).ae_ne (0 : E)] with x hx
  simp [sphereDirection, hx]

end OperatorPhaseRetrieval

end
