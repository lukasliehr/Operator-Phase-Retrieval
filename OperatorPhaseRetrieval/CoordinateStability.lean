module

public import OperatorPhaseRetrieval.PairModulus
public import OperatorPhaseRetrieval.OrthogonalReduction

@[expose] public section

noncomputable section

open MeasureTheory Set Metric

namespace OperatorPhaseRetrieval

variable {ι : Type*} [Fintype ι]

theorem coordinateModulus_dist_mono (u v f g : EuclideanSpace ℂ ι)
    (h : ∀ i, |‖u i‖ - ‖v i‖| ≤ |‖f i‖ - ‖g i‖|) :
    dist (coordinateModulus u) (coordinateModulus v) ≤
      dist (coordinateModulus f) (coordinateModulus g) := by
  apply (sq_le_sq₀ dist_nonneg dist_nonneg).mp
  rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  apply (sq_le_sq₀ dist_nonneg dist_nonneg).mpr
  change dist ‖u i‖ ‖v i‖ ≤ dist ‖f i‖ ‖g i‖
  simpa only [Real.dist_eq] using h i

theorem coordinateModulus_dist_smul (a : ℂ) (f g : EuclideanSpace ℂ ι) :
    dist (coordinateModulus (a • f)) (coordinateModulus (a • g)) =
      ‖a‖ * dist (coordinateModulus f) (coordinateModulus g) := by
  rw [coordinateModulus_smul, coordinateModulus_smul, dist_smul₀, Real.norm_of_nonneg (norm_nonneg a)]

/-- Homogeneity and the orthogonal reduction extend a lower bound on normalized orthogonal
pairs to all pairs of finite-dimensional vectors. -/
theorem coordinateStability_of_normalized
    (U : Fin 5 → HaarUnitary (EuclideanSpace ℂ ι)) (c : ℝ)
    (hU : ∀ p ∈ normalizedOrthogonalPairs, ∃ j, c ≤ pairModulusDistance (U j) p) :
    ∀ f g : EuclideanSpace ℂ ι, ∃ j,
      c * phaseDistance f g ≤
        dist (coordinateModulus ((U j : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) f))
          (coordinateModulus ((U j : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) g)) := by
  intro f g
  by_cases hd : phaseDistance f g = 0
  · refine ⟨0, ?_⟩
    simpa only [hd, mul_zero] using dist_nonneg
  have hdpos : 0 < phaseDistance f g :=
    lt_of_le_of_ne (phaseDistance_nonneg f g) (Ne.symm hd)
  obtain ⟨u, v, _, _, huv, hn, hpoint⟩ := orthogonal_reduction f g
  let a : ℝ := (phaseDistance f g)⁻¹
  have ha : 0 < a := inv_pos.mpr hdpos
  let p : UnitaryPair ι := WithLp.toLp 2 (((a : ℂ) • u), ((a : ℂ) • v))
  have hp : p ∈ normalizedOrthogonalPairs := by
    constructor
    · change inner ℂ ((a : ℂ) • u) ((a : ℂ) • v) = 0
      simp only [inner_smul_left, inner_smul_right, huv, mul_zero]
    · change ‖(a : ℂ) • u‖ ^ 2 + ‖(a : ℂ) • v‖ ^ 2 = 1
      simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, mul_pow]
      rw [← mul_add, hn]
      dsimp [a]
      rw [← mul_pow, inv_mul_cancel₀ hd, one_pow]
  obtain ⟨j, hj⟩ := hU p hp
  let T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι := U j
  have hscale : pairModulusDistance (U j) p =
      a * dist (coordinateModulus (T u)) (coordinateModulus (T v)) := by
    change dist (coordinateModulus (T ((a : ℂ) • u)))
      (coordinateModulus (T ((a : ℂ) • v))) = _
    rw [map_smul, map_smul, coordinateModulus_dist_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ha]
  rw [hscale] at hj
  have hmul := mul_le_mul_of_nonneg_left hj hdpos.le
  have hcancel : phaseDistance f g *
      (a * dist (coordinateModulus (T u)) (coordinateModulus (T v))) =
        dist (coordinateModulus (T u)) (coordinateModulus (T v)) := by
    dsimp [a]
    rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  rw [hcancel] at hmul
  have hfinal : c * phaseDistance f g ≤ dist (coordinateModulus (T u)) (coordinateModulus (T v)) := by
    simpa only [mul_comm] using hmul
  refine ⟨j, hfinal.trans ?_⟩
  apply coordinateModulus_dist_mono
  intro i
  let Ti : EuclideanSpace ℂ ι →ₗ[ℂ] ℂ :=
    (LinearMap.proj i).comp ((WithLp.linearEquiv 2 ℂ (ι → ℂ)).toLinearMap.comp T.toLinearMap)
  exact hpoint Ti

end OperatorPhaseRetrieval

end
