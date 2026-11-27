import OperatorPhaseRetrieval.ExpressionBounds

/-! # Hilbert--Schmidt bounds for the finite-dimensional models -/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace OperatorPhaseRetrieval

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι : Type*} [Fintype ι]

/-- The Hilbert--Schmidt norm computed in an orthonormal basis. -/
def basisHilbertSchmidtNorm (b : OrthonormalBasis ι ℂ H) (A : H →L[ℂ] H) : ℝ :=
  ‖WithLp.toLp 2 (fun i => A (b i))‖

theorem basisHilbertSchmidtNorm_sq (b : OrthonormalBasis ι ℂ H) (A : H →L[ℂ] H) :
    basisHilbertSchmidtNorm b A ^ 2 = ∑ i, ‖A (b i)‖ ^ 2 := by
  exact PiLp.norm_sq_eq_of_L2 _ _

theorem opNorm_le_basisHilbertSchmidtNorm (b : OrthonormalBasis ι ℂ H)
    (A : H →L[ℂ] H) : ‖A‖ ≤ basisHilbertSchmidtNorm b A := by
  classical
  have hb0 : 0 ≤ basisHilbertSchmidtNorm b A := norm_nonneg _
  apply ContinuousLinearMap.opNorm_le_bound _ hb0
  intro x
  have hn : ∑ i, ‖b.repr x i‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← PiLp.norm_sq_eq_of_L2, b.repr.norm_map]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => ‖b.repr x i‖) (fun i => ‖A (b i)‖)
  rw [hn, ← basisHilbertSchmidtNorm_sq, ← mul_pow] at hcs
  have hs : ∑ i, ‖b.repr x i‖ * ‖A (b i)‖ ≤ ‖x‖ * basisHilbertSchmidtNorm b A :=
    (sq_le_sq₀ (Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp hcs
  calc
    ‖A x‖ = ‖∑ i, b.repr x i • A (b i)‖ := by
      congr 1
      nth_rw 1 [← b.sum_repr x]
      simp only [map_sum, map_smul]
    _ ≤ ∑ i, ‖b.repr x i‖ * ‖A (b i)‖ := by
      simpa only [norm_smul] using norm_sum_le Finset.univ (fun i => b.repr x i • A (b i))
    _ ≤ _ := by simpa only [mul_comm] using hs

/-- Product Hilbert--Schmidt metric for the six matrices of the expressions. -/
def hilbertSchmidtFamilyDistance (b : OrthonormalBasis ι ℂ H)
    (U V : Fin 6 → H ≃ₗᵢ[ℂ] H) : ℝ :=
  ‖WithLp.toLp 2 (fun j => WithLp.toLp 2 (fun i => U j (b i) - V j (b i)))‖

theorem hilbertSchmidtFamilyDistance_sq (b : OrthonormalBasis ι ℂ H)
    (U V : Fin 6 → H ≃ₗᵢ[ℂ] H) :
    hilbertSchmidtFamilyDistance b U V ^ 2 = ∑ j, ∑ i, ‖U j (b i) - V j (b i)‖ ^ 2 := by
  simp only [hilbertSchmidtFamilyDistance, PiLp.norm_sq_eq_of_L2]

theorem unitaryFamilyDistance_le_hilbertSchmidt (b : OrthonormalBasis ι ℂ H)
    (U V : Fin 6 → H ≃ₗᵢ[ℂ] H) :
    unitaryFamilyDistance U V ≤ hilbertSchmidtFamilyDistance b U V := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro j
  exact (opNorm_le_basisHilbertSchmidtNorm b _).trans
    (PiLp.norm_apply_le (WithLp.toLp 2 (fun k =>
      WithLp.toLp 2 (fun i => U k (b i) - V k (b i)))) j)

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- Norm and Lipschitz bounds for expressions in the product Hilbert--Schmidt distance, with
recursive constants. The ambient L² norm may be normalized counting measure. -/
theorem expression_hilbertSchmidt_bounds (t : StabilityExpression)
    (b : OrthonormalBasis ι ℂ (L2 μ)) (U V : Fin 6 → L2 μ ≃ₗᵢ[ℂ] L2 μ) :
    ‖t.eval U‖ ≤ t.radius ∧
      ‖t.eval U - t.eval V‖ ≤ t.lipBound * hilbertSchmidtFamilyDistance b U V := by
  refine ⟨t.eval_norm_le U, (t.eval_sub_le U V).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (unitaryFamilyDistance_le_hilbertSchmidt b U V)
    (NNReal.coe_nonneg _)

/-- Positive constants in the bounds for expressions, chosen before the probability space and its
dimension. The estimate is thus uniform over all normalized finite models. -/
theorem expression_positive_hilbertSchmidt_bounds (t : StabilityExpression) :
    ∃ R L : ℝ, 0 < R ∧ 0 < L ∧
      ∀ (X : Type*) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
        (ι : Type*) [Fintype ι] (b : OrthonormalBasis ι ℂ (L2 μ))
        (U V : Fin 6 → L2 μ ≃ₗᵢ[ℂ] L2 μ),
        ‖t.eval U‖ ≤ R ∧
          ‖t.eval U - t.eval V‖ ≤ L * hilbertSchmidtFamilyDistance b U V := by
  refine ⟨t.radius + 1, t.lipBound + 1, by positivity, by positivity, ?_⟩
  intro X _ μ _ ι _ b U V
  obtain ⟨h₁, h₂⟩ := expression_hilbertSchmidt_bounds t b U V
  refine ⟨h₁.trans (by linarith), h₂.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

end OperatorPhaseRetrieval

end
