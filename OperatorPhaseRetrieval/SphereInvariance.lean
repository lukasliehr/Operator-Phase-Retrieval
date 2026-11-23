import OperatorPhaseRetrieval.SphereCaps

/-!
# Invariance of canonical sphere measure

Real linear isometric equivalences preserve the surface measure constructed
from ambient volume, and therefore also its normalized probability measure.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal Pointwise

namespace OperatorPhaseRetrieval

variable {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    [MeasurableSpace G] [BorelSpace G]

def unitSphereEquiv (e : E ≃ₗᵢ[ℝ] G) : sphere (0 : E) 1 ≃ᵢ sphere (0 : G) 1 where
  toFun x := ⟨e x, by simpa only [mem_sphere, dist_zero_right, e.norm_map] using x.property⟩
  invFun y := ⟨e.symm y, by simpa only [mem_sphere, dist_zero_right, e.symm.norm_map] using y.property⟩
  left_inv x := by ext; exact e.symm_apply_apply x
  right_inv y := by ext; exact e.apply_symm_apply y
  isometry_toFun x y := e.isometry x y

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] in
theorem sphere_sector_preimage (e : E ≃ₗᵢ[ℝ] G) (s : Set (sphere (0 : G) 1)) :
    e ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s)) =
      Ioo (0 : ℝ) 1 • ((↑) '' (unitSphereEquiv e ⁻¹' s)) := by
  ext x
  constructor
  · rintro ⟨t, ht, _, ⟨z, hz, rfl⟩, h⟩
    refine ⟨t, ht, _, ⟨(unitSphereEquiv e).symm z, ?_, rfl⟩, ?_⟩
    · simpa only [mem_preimage, (unitSphereEquiv e).apply_symm_apply] using hz
    · apply e.injective
      change e (t • e.symm (z : G)) = e x
      simpa only [map_smul, e.apply_symm_apply] using h
  · rintro ⟨t, ht, _, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨t, ht, _, ⟨unitSphereEquiv e z, hz, rfl⟩, (e.map_smul t z).symm⟩

theorem toSphere_measurePreserving (e : E ≃ₗᵢ[ℝ] G) :
    MeasurePreserving (unitSphereEquiv e) (volume : Measure E).toSphere (volume : Measure G).toSphere := by
  have hm := (unitSphereEquiv e).continuous.measurable
  refine ⟨hm, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hm hs, Measure.toSphere_apply' _ (hm hs), Measure.toSphere_apply' _ hs]
  have hv := e.measurePreserving.measure_preimage_emb e.toMeasurableEquiv.measurableEmbedding
    (Ioo (0 : ℝ) 1 • ((↑) '' s))
  rw [sphere_sector_preimage] at hv
  rw [hv, e.toLinearEquiv.finrank_eq]

theorem uniformSphere_measurePreserving [Nontrivial E] [Nontrivial G] (e : E ≃ₗᵢ[ℝ] G) :
    MeasurePreserving (unitSphereEquiv e) (uniformSphere E : Measure _) (uniformSphere G : Measure _) := by
  have hm := (unitSphereEquiv e).continuous.measurable
  refine ⟨hm, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hm hs, uniformSphere_apply, uniformSphere_apply,
    toSphere_univ_isometry e]
  congr 1
  exact (toSphere_measurePreserving e).measure_preimage (s := s) hs.nullMeasurableSet

end OperatorPhaseRetrieval

end
