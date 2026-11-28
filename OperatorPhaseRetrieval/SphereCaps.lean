module

public import OperatorPhaseRetrieval.MathlibImports
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

@[expose] public section

/-!
# Spherical-cap probabilities

The spherical cap estimate is proved for canonical normalized surface measure, including centers
in an ambient metric space. The proof compares the radial sector of a cap with
a cylinder and bounds the unit-ball volume below by a smaller cylinder. It needs
neither a surface Jacobian calculation nor a gamma-function volume formula.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Pointwise

namespace OperatorPhaseRetrieval

theorem cap_sector_preimage_isometry {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (e : E ≃ₗᵢ[ℝ] G) (y : E) (ρ : ℝ) :
    e ⁻¹' (Ioo (0 : ℝ) 1 • (closedBall (e y) ρ ∩ sphere 0 1)) =
      Ioo (0 : ℝ) 1 • (closedBall y ρ ∩ sphere 0 1) := by
  have he (w : E) : e w ∈ closedBall (e y) ρ ∩ sphere 0 1 ↔ w ∈ closedBall y ρ ∩ sphere 0 1 := by
    simp only [mem_inter_iff, mem_closedBall, mem_sphere, dist_zero_right, e.dist_map, e.norm_map]
  ext x
  constructor
  · rintro ⟨t, ht, z, hz, htx⟩
    refine ⟨t, ht, e.symm z, (he _).mp (by simpa only [e.apply_symm_apply] using hz), ?_⟩
    apply e.injective
    simpa only [map_smul, e.apply_symm_apply] using htx
  · rintro ⟨t, ht, z, hz, rfl⟩
    exact ⟨t, ht, e z, (he z).mpr hz, (e.map_smul t z).symm⟩

theorem coe_sphere_cap {E : Type*} [PseudoMetricSpace E] (y : E) (ρ : ℝ) (o : E) (R : ℝ) :
    ((↑) '' {z : sphere o R | dist (z : E) y ≤ ρ}) = closedBall y ρ ∩ sphere o R := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨hz, z.property⟩
  · rintro ⟨hx, hS⟩
    exact ⟨⟨x, hS⟩, hx, rfl⟩

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

def sphereNorth : WithLp 2 (ℝ × F) := WithLp.toLp 2 (1, 0)

theorem volume_product_cylinder (a b r : ℝ) :
    volume {x : WithLp 2 (ℝ × F) | x.fst ∈ Ioo a b ∧ x.snd ∈ closedBall 0 r} =
      ENNReal.ofReal (b - a) * volume (closedBall (0 : F) r) := by
  have h := (WithLp.volume_preserving_ofLp ℝ F).measure_preimage (s := Ioo a b ×ˢ closedBall (0 : F) r)
    ((measurableSet_Ioo.prod measurableSet_closedBall).nullMeasurableSet)
  change volume ((WithLp.ofLp : WithLp 2 (ℝ × F) → ℝ × F) ⁻¹'
    (Ioo a b ×ˢ closedBall (0 : F) r)) = _
  rw [h, volume_eq_prod, Measure.prod_prod, Real.volume_Ioo]

theorem volume_product_open_cylinder (a b r : ℝ) :
    volume {x : WithLp 2 (ℝ × F) | x.fst ∈ Ioo a b ∧ x.snd ∈ ball 0 r} =
      ENNReal.ofReal (b - a) * volume (ball (0 : F) r) := by
  have h := (WithLp.volume_preserving_ofLp ℝ F).measure_preimage (s := Ioo a b ×ˢ ball (0 : F) r)
    ((measurableSet_Ioo.prod measurableSet_ball).nullMeasurableSet)
  change volume ((WithLp.ofLp : WithLp 2 (ℝ × F) → ℝ × F) ⁻¹'
    (Ioo a b ×ˢ ball (0 : F) r)) = _
  rw [h, volume_eq_prod, Measure.prod_prod, Real.volume_Ioo]

omit [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
theorem half_cylinder_subset_unitBall :
    {x : WithLp 2 (ℝ × F) | x.fst ∈ Ioo (-(1 / 2)) (1 / 2) ∧ x.snd ∈ ball 0 (1 / 2)} ⊆
      ball 0 1 := by
  intro x hx
  have hx1 : |x.fst| < 1 / 2 := abs_lt.mpr hx.1
  have hx2 : ‖x.snd‖ < 1 / 2 := by simpa using hx.2
  rw [mem_ball_zero_iff]
  have he := WithLp.prod_norm_sq_eq_of_L2 x
  simp only [Real.norm_eq_abs] at he
  nlinarith [norm_nonneg x, abs_nonneg x.fst, norm_nonneg x.snd]

theorem volume_unitBall_ge_half_cylinder :
    ENNReal.ofReal ((1 / 2 : ℝ) ^ Module.finrank ℝ F) * volume (ball (0 : F) 1) ≤
      volume (ball (0 : WithLp 2 (ℝ × F)) 1) := by
  have h := (volume : Measure (WithLp 2 (ℝ × F))).mono (half_cylinder_subset_unitBall F)
  change volume {x : WithLp 2 (ℝ × F) | x.fst ∈ Ioo (-(1 / 2)) (1 / 2) ∧ x.snd ∈ ball 0 (1 / 2)} ≤ volume (ball (0 : WithLp 2 (ℝ × F)) 1) at h
  rw [volume_product_open_cylinder, Measure.addHaar_ball_of_pos volume _ (by norm_num : (0 : ℝ) < 1 / 2)] at h
  norm_num at h ⊢
  exact h

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
theorem north_cap_sector_subset_cylinder (ρ : ℝ) (hρ : ρ ≤ 1 / 2) :
    Ioo (0 : ℝ) 1 •
      ((↑) '' {y : sphere (0 : WithLp 2 (ℝ × F)) 1 | dist (y : WithLp 2 (ℝ × F)) (sphereNorth F) ≤ ρ}) ⊆
      {x : WithLp 2 (ℝ × F) | x.fst ∈ Ioo 0 1 ∧ x.snd ∈ closedBall 0 ρ} := by
  rintro x ⟨t, ht, _, ⟨y, hy, rfl⟩, rfl⟩
  change dist (y : WithLp 2 (ℝ × F)) (sphereNorth F) ≤ ρ at hy
  have hyn : ‖(y : WithLp 2 (ℝ × F))‖ = 1 := by simp
  have hf : |(y : WithLp 2 (ℝ × F)).fst - 1| ≤ ρ := by
    have h := (WithLp.norm_fst_le ℝ ((y : WithLp 2 (ℝ × F)) - sphereNorth F)).trans (by simpa only [dist_eq_norm] using hy)
    simpa only [dist_eq_norm, WithLp.sub_fst, sphereNorth, WithLp.toLp_fst, Real.norm_eq_abs] using h
  have hs : ‖(y : WithLp 2 (ℝ × F)).snd‖ ≤ ρ := by
    have h := WithLp.norm_snd_le ℝ ((y : WithLp 2 (ℝ × F)) - sphereNorth F)
    have := h.trans (by simpa only [dist_eq_norm] using hy)
    simpa only [dist_eq_norm, WithLp.sub_snd, sphereNorth, WithLp.toLp_snd, sub_zero] using this
  have hf1 : |(y : WithLp 2 (ℝ × F)).fst| ≤ 1 := by
    simpa only [hyn, Real.norm_eq_abs] using WithLp.norm_fst_le ℝ (y : WithLp 2 (ℝ × F))
  have hfpos : 0 < (y : WithLp 2 (ℝ × F)).fst := by
    have := (abs_le.mp hf).1
    linarith
  constructor
  · change 0 < t * (y : WithLp 2 (ℝ × F)).fst ∧ t * (y : WithLp 2 (ℝ × F)).fst < 1
    constructor
    · exact mul_pos ht.1 hfpos
    · have := (abs_le.mp hf1).2
      nlinarith [ht.1, ht.2]
  · rw [mem_closedBall_zero_iff]
    simp only [WithLp.smul_snd, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
    nlinarith [ht.2, norm_nonneg (y : WithLp 2 (ℝ × F)).snd]

theorem north_cap_sector_volume_le (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 2) :
    (volume : Measure (WithLp 2 (ℝ × F))) (Ioo (0 : ℝ) 1 •
      ((↑) '' {y : sphere (0 : WithLp 2 (ℝ × F)) 1 | dist (y : WithLp 2 (ℝ × F)) (sphereNorth F) ≤ ρ})) ≤
      ENNReal.ofReal ((2 * ρ) ^ Module.finrank ℝ F) * volume (ball (0 : WithLp 2 (ℝ × F)) 1) := by
  calc
    _ ≤ volume {x : WithLp 2 (ℝ × F) | x.fst ∈ Ioo 0 1 ∧ x.snd ∈ closedBall 0 ρ} :=
      measure_mono (north_cap_sector_subset_cylinder F ρ hρ)
    _ = ENNReal.ofReal (ρ ^ Module.finrank ℝ F) * volume (ball (0 : F) 1) := by
      rw [volume_product_cylinder, Measure.addHaar_closedBall volume _ hρ0]
      norm_num
    _ = ENNReal.ofReal ((2 * ρ) ^ Module.finrank ℝ F) *
      (ENNReal.ofReal ((1 / 2 : ℝ) ^ Module.finrank ℝ F) * volume (ball (0 : F) 1)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [← mul_pow]
        congr 1
        ring
    _ ≤ _ := by gcongr; exact volume_unitBall_ge_half_cylinder F

/-- The cap estimate at the north pole, before normalization of sphere measure. -/
theorem north_cap_toSphere_le (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 2) :
    (volume : Measure (WithLp 2 (ℝ × F))).toSphere
      {y | dist (y : WithLp 2 (ℝ × F)) (sphereNorth F) ≤ ρ} ≤
      ENNReal.ofReal ((2 * ρ) ^ Module.finrank ℝ F) *
        (volume : Measure (WithLp 2 (ℝ × F))).toSphere univ := by
  rw [Measure.toSphere_apply' _
    (measurableSet_le (continuous_subtype_val.dist continuous_const).measurable measurable_const),
    Measure.toSphere_apply_univ]
  calc
    _ ≤ (Module.finrank ℝ (WithLp 2 (ℝ × F)) : ℝ≥0∞) *
      (ENNReal.ofReal ((2 * ρ) ^ Module.finrank ℝ F) * volume (ball (0 : WithLp 2 (ℝ × F)) 1)) :=
        by gcongr; exact north_cap_sector_volume_le F ρ hρ0 hρ
    _ = _ := by ring

omit [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
theorem sphereNorth_norm : ‖sphereNorth F‖ = 1 := by simp [sphereNorth]

theorem unit_center_cap_toSphere_le (y : WithLp 2 (ℝ × F)) (hy : ‖y‖ = 1)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 2) :
    (volume : Measure (WithLp 2 (ℝ × F))).toSphere {z | dist (z : WithLp 2 (ℝ × F)) y ≤ ρ} ≤
      ENNReal.ofReal ((2 * ρ) ^ Module.finrank ℝ F) *
        (volume : Measure (WithLp 2 (ℝ × F))).toSphere univ := by
  let e : WithLp 2 (ℝ × F) ≃ₗᵢ[ℝ] WithLp 2 (ℝ × F) :=
    (ℝ ∙ (y - sphereNorth F))ᗮ.reflection
  have hey : e y = sphereNorth F := Submodule.reflection_sub (hy.trans (sphereNorth_norm F).symm)
  have hvol : volume (Ioo (0 : ℝ) 1 • (closedBall y ρ ∩ sphere 0 1)) =
      volume (Ioo (0 : ℝ) 1 • (closedBall (sphereNorth F) ρ ∩ sphere 0 1)) := by
    rw [← cap_sector_preimage_isometry e y ρ, hey]
    exact e.measurePreserving.measure_preimage_emb e.toMeasurableEquiv.measurableEmbedding _
  have hmeas (w : WithLp 2 (ℝ × F)) :
      MeasurableSet {z : sphere (0 : WithLp 2 (ℝ × F)) 1 | dist (z : WithLp 2 (ℝ × F)) w ≤ ρ} :=
    measurableSet_le (continuous_subtype_val.dist continuous_const).measurable measurable_const
  have h := north_cap_toSphere_le F ρ hρ0 hρ
  rw [Measure.toSphere_apply' _ (hmeas (sphereNorth F)), coe_sphere_cap] at h
  rw [Measure.toSphere_apply' _ (hmeas y), coe_sphere_cap, hvol]
  exact h

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] in
theorem toSphere_cap_isometry {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    [MeasurableSpace G] [BorelSpace G]
    (e : E ≃ₗᵢ[ℝ] G) (y : E) (ρ : ℝ) :
    (volume : Measure E).toSphere {z | dist (z : E) y ≤ ρ} =
      (volume : Measure G).toSphere {z | dist (z : G) (e y) ≤ ρ} := by
  rw [Measure.toSphere_apply' _
    (measurableSet_le (continuous_subtype_val.dist continuous_const).measurable measurable_const),
    Measure.toSphere_apply' _
    (measurableSet_le (continuous_subtype_val.dist continuous_const).measurable measurable_const),
    coe_sphere_cap, coe_sphere_cap]
  have hv := e.measurePreserving.measure_preimage_emb e.toMeasurableEquiv.measurableEmbedding
    (Ioo (0 : ℝ) 1 • (closedBall (e y) ρ ∩ sphere 0 1))
  rw [cap_sector_preimage_isometry] at hv
  rw [hv, e.toLinearEquiv.finrank_eq]

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] in
theorem toSphere_univ_isometry {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    [MeasurableSpace G] [BorelSpace G]
    (e : E ≃ₗᵢ[ℝ] G) :
    (volume : Measure E).toSphere univ = (volume : Measure G).toSphere univ := by
  rw [Measure.toSphere_apply_univ, Measure.toSphere_apply_univ]
  have he : e ⁻¹' ball (0 : G) 1 = ball (0 : E) 1 := by
    ext x
    simp only [mem_preimage, mem_ball_zero_iff, e.norm_map]
  have hv := e.measurePreserving.measure_preimage_emb e.toMeasurableEquiv.measurableEmbedding
    (ball (0 : G) 1)
  rw [he] at hv
  rw [hv, e.toLinearEquiv.finrank_eq]

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] in
/-- A cap of radius `ρ ≤ 1/2` at a unit vector in any finite-dimensional real
Hilbert space, with sphere measure before normalization. -/
theorem unit_center_toSphere_cap_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (y : E) (hy : ‖y‖ = 1) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 2) :
    (volume : Measure E).toSphere {z | dist (z : E) y ≤ ρ} ≤
      ENNReal.ofReal ((2 * ρ) ^ (Module.finrank ℝ E - 1)) * (volume : Measure E).toSphere univ := by
  let K : Submodule ℝ E := ℝ ∙ y
  let G := Kᗮ
  let e : E ≃ₗᵢ[ℝ] WithLp 2 (ℝ × G) := K.orthogonalDecomposition.trans
    (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.toSpanUnitSingleton y hy).symm
      (LinearIsometryEquiv.refl ℝ G))
  have hd : Module.finrank ℝ G = Module.finrank ℝ E - 1 := by
    have he := K.finrank_add_finrank_orthogonal
    have hK : Module.finrank ℝ K = 1 := finrank_span_singleton (by intro hz; simp [hz] at hy)
    change Module.finrank ℝ Kᗮ = Module.finrank ℝ E - 1
    omega
  rw [toSphere_cap_isometry e, toSphere_univ_isometry e, ← hd]
  exact unit_center_cap_toSphere_le G (e y) (by simpa using hy) ρ hρ0 hρ

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] in
/-- The spherical-cap estimate also allows the center to lie in an ambient metric
space into which the Euclidean space is isometrically embedded. -/
theorem ambient_toSphere_cap_le {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [PseudoMetricSpace G]
    (f : E → G) (hf : Isometry f) (z : G) (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 4) :
    (volume : Measure E).toSphere {y | dist (f (y : E)) z ≤ r} ≤
      ENNReal.ofReal ((4 * r) ^ (Module.finrank ℝ E - 1)) * (volume : Measure E).toSphere univ := by
  by_cases h : ({y : sphere (0 : E) 1 | dist (f (y : E)) z ≤ r} : Set _).Nonempty
  · obtain ⟨y0, hy0⟩ := h
    have hy0' : dist (f (y0 : E)) z ≤ r := hy0
    calc
      _ ≤ (volume : Measure E).toSphere {y | dist (y : E) (y0 : E) ≤ 2 * r} := by
        apply measure_mono
        intro y hy
        have hy' : dist (f (y : E)) z ≤ r := hy
        have ht := dist_triangle (f (y : E)) z (f (y0 : E))
        rw [hf.dist_eq, dist_comm z] at ht
        change dist (y : E) (y0 : E) ≤ 2 * r
        linarith
      _ ≤ ENNReal.ofReal ((2 * (2 * r)) ^ (Module.finrank ℝ E - 1)) *
          (volume : Measure E).toSphere univ :=
        unit_center_toSphere_cap_le (y0 : E) (by simp) (2 * r) (by positivity) (by linarith)
      _ = _ := by congr 3; ring
  · rw [Set.not_nonempty_iff_eq_empty.mp h, measure_empty]
    exact bot_le

end OperatorPhaseRetrieval

namespace OperatorPhaseRetrieval

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- Normalized canonical surface measure on the unit sphere of a real Hilbert space. -/
def uniformSphere : ProbabilityMeasure (sphere (0 : E) 1) := by
  let σ := (volume : Measure E).toSphere
  have : NeZero σ := ⟨Measure.toSphere_ne_zero volume⟩
  exact ⟨(σ univ)⁻¹ • σ, inferInstance⟩

theorem uniformSphere_apply (s : Set (sphere (0 : E) 1)) :
    (uniformSphere E : Measure (sphere (0 : E) 1)) s =
      ((volume : Measure E).toSphere univ)⁻¹ * (volume : Measure E).toSphere s := by
  rfl

/-- The spherical cap estimate: the probability of an ambient radius-`r` ball under uniform sphere
measure is at most `(4r)^(D-1)`. In particular this applies for every `D ≥ 2`. -/
theorem uniformSphere_cap_le {G : Type*} [PseudoMetricSpace G]
    (f : E → G) (hf : Isometry f) (z : G) (r : ℝ) (hr0 : 0 < r) (hr : r ≤ 1 / 4) :
    (uniformSphere E : Measure (sphere (0 : E) 1)) {y | dist (f (y : E)) z ≤ r} ≤
      ENNReal.ofReal ((4 * r) ^ (Module.finrank ℝ E - 1)) := by
  rw [uniformSphere_apply]
  have h0 : (volume : Measure E).toSphere univ ≠ 0 :=
    Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero volume)
  have htop : (volume : Measure E).toSphere univ ≠ ⊤ := measure_ne_top _ _
  calc
    _ ≤ ((volume : Measure E).toSphere univ)⁻¹ *
      (ENNReal.ofReal ((4 * r) ^ (Module.finrank ℝ E - 1)) * (volume : Measure E).toSphere univ) :=
        by gcongr; exact ambient_toSphere_cap_le f hf z r hr0.le hr
    _ = _ := by
      rw [mul_left_comm, ENNReal.inv_mul_cancel h0 htop, mul_one]

end OperatorPhaseRetrieval

end
