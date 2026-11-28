module

public import OperatorPhaseRetrieval.SmoothModulus

@[expose] public section

noncomputable section

namespace OperatorPhaseRetrieval

variable (ι : Type*) [Fintype ι]

/-- Apply a scalar function to every Euclidean coordinate. -/
def euclideanCoordinateMap (ψ : ℂ → ℂ) (x : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => ψ (x i))

theorem euclideanCoordinateMap_sub_le (ψ : ℂ → ℂ) (hψ : LipschitzWith 1 ψ)
    (x y : EuclideanSpace ℂ ι) :
    ‖euclideanCoordinateMap ι ψ x - euclideanCoordinateMap ι ψ y‖ ≤ ‖x - y‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro i _
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
  simpa [euclideanCoordinateMap] using hψ.norm_sub_le (x i) (y i)

theorem euclideanCoordinateMap_lipschitz (ψ : ℂ → ℂ) (hψ : LipschitzWith 1 ψ) :
    LipschitzWith 1 (euclideanCoordinateMap ι ψ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using euclideanCoordinateMap_sub_le ι ψ hψ x y

omit [Fintype ι] in
theorem euclideanCoordinateMap_zero (ψ : ℂ → ℂ) (hzero : ψ 0 = 0) :
    euclideanCoordinateMap ι ψ 0 = 0 := by
  ext i
  exact hzero

theorem euclideanCoordinateMap_norm_le (ψ : ℂ → ℂ) (hψ : LipschitzWith 1 ψ) (hzero : ψ 0 = 0)
    (x : EuclideanSpace ℂ ι) : ‖euclideanCoordinateMap ι ψ x‖ ≤ ‖x‖ := by
  simpa only [euclideanCoordinateMap_zero ι ψ hzero, sub_zero] using
    euclideanCoordinateMap_sub_le ι ψ hψ x 0

theorem euclideanCoordinateMap_contDiff (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ⊤ ψ) :
    ContDiff ℝ ⊤ (euclideanCoordinateMap ι ψ) := by
  apply PiLp.contDiff_toLp.comp
  apply contDiff_pi.mpr
  intro i
  exact hψ.comp (contDiff_piLp_apply 2)

theorem euclideanCoordinateMap_error_le (ψ φ : ℂ → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ z, ‖ψ z - φ z‖ ≤ ε) (x : EuclideanSpace ℂ ι) :
    ‖euclideanCoordinateMap ι ψ x - euclideanCoordinateMap ι φ x‖ ≤
      Real.sqrt (Fintype.card ι) * ε := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  calc
    _ ≤ ∑ _i : ι, ε ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact (sq_le_sq₀ (norm_nonneg _) hε).mpr (h (x i))
    _ = _ := by simp

end OperatorPhaseRetrieval

end
