import OperatorPhaseRetrieval.HaarSmallBall

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace OperatorPhaseRetrieval

variable {ι : Type*} [Fintype ι]

theorem coordinateModulus_dist_le (x y : EuclideanSpace ℂ ι) :
    dist (coordinateModulus x) (coordinateModulus y) ≤ dist x y := by
  apply (sq_le_sq₀ dist_nonneg dist_nonneg).mp
  rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  apply (sq_le_sq₀ dist_nonneg dist_nonneg).mpr
  change dist ‖x i‖ ‖y i‖ ≤ dist (x i) (y i)
  rw [Real.dist_eq, dist_eq_norm]
  exact abs_norm_sub_norm_le (x i) (y i)

abbrev UnitaryPair (ι : Type*) := WithLp 2 (EuclideanSpace ℂ ι × EuclideanSpace ℂ ι)

def normalizedOrthogonalPairs : Set (UnitaryPair ι) :=
  {p | inner ℂ p.fst p.snd = 0 ∧ ‖p.fst‖ ^ 2 + ‖p.snd‖ ^ 2 = 1}

theorem normalizedOrthogonalPairs_norm (p : UnitaryPair ι) (hp : p ∈ normalizedOrthogonalPairs) :
    ‖p‖ = 1 := by
  have h := WithLp.prod_norm_sq_eq_of_L2 p
  have hp2 := hp.2
  nlinarith [norm_nonneg p]

theorem unitaryPair_real_finrank : Module.finrank ℝ (UnitaryPair ι) = 4 * Fintype.card ι := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (UnitaryPair ι), Complex.finrank_real_complex,
    (WithLp.linearEquiv 2 ℂ (EuclideanSpace ℂ ι × EuclideanSpace ℂ ι)).finrank_eq,
    Module.finrank_prod, finrank_euclideanSpace]
  omega

def pairModulusDistance (u : HaarUnitary (EuclideanSpace ℂ ι)) (p : UnitaryPair ι) : ℝ :=
  dist (coordinateModulus ((u : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) p.fst))
    (coordinateModulus ((u : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) p.snd))

theorem pairModulusDistance_lipschitz (u : HaarUnitary (EuclideanSpace ℂ ι))
    (p q : UnitaryPair ι) :
    |pairModulusDistance u p - pairModulusDistance u q| ≤ Real.sqrt 2 * ‖p - q‖ := by
  let U := Unitary.linearIsometryEquiv u
  have h := dist_dist_dist_le
    (coordinateModulus (U p.fst)) (coordinateModulus (U p.snd))
    (coordinateModulus (U q.fst)) (coordinateModulus (U q.snd))
  have h1 := coordinateModulus_dist_le (U p.fst) (U q.fst)
  have h2 := coordinateModulus_dist_le (U p.snd) (U q.snd)
  rw [U.dist_map] at h1 h2
  have hsum : ‖p.fst - q.fst‖ + ‖p.snd - q.snd‖ ≤ Real.sqrt 2 * ‖p - q‖ := by
    have he := WithLp.prod_norm_sq_eq_of_L2 (p - q)
    simp only [WithLp.sub_fst, WithLp.sub_snd] at he
    have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hpos := Real.sqrt_nonneg (2 : ℝ)
    have hmul : 0 ≤ Real.sqrt 2 * ‖p - q‖ := mul_nonneg hpos (norm_nonneg _)
    have hsq : (‖p.fst - q.fst‖ + ‖p.snd - q.snd‖) ^ 2 ≤ (Real.sqrt 2 * ‖p - q‖) ^ 2 := by
      rw [mul_pow, hs]
      nlinarith [sq_nonneg (‖p.fst - q.fst‖ - ‖p.snd - q.snd‖)]
    exact (sq_le_sq₀ (by positivity) hmul).mp hsq
  change |pairModulusDistance u p - pairModulusDistance u q| ≤ _
  change |pairModulusDistance u p - pairModulusDistance u q| ≤ _ at h
  exact h.trans ((add_le_add h1 h2).trans (by simpa only [dist_eq_norm] using hsum))

end OperatorPhaseRetrieval

end
