module

public import OperatorPhaseRetrieval.FiniteExpressionContinuity
public import OperatorPhaseRetrieval.HilbertSchmidtBounds

@[expose] public section

noncomputable section

open MeasureTheory

namespace OperatorPhaseRetrieval

variable (ι : Type*) [Fintype ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

def haarFamilyHilbertSchmidtDistance
    (U V : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) : ℝ :=
  hilbertSchmidtFamilyDistance (EuclideanSpace.basisFun ι ℂ)
    (fun j => Unitary.linearIsometryEquiv (U j)) (fun j => Unitary.linearIsometryEquiv (V j))

theorem finiteHaarModel_hilbertSchmidtDistance
    (U V : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) :
    hilbertSchmidtFamilyDistance ((EuclideanSpace.basisFun ι ℂ).map (finiteL2Equiv ι ℂ))
      (finiteHaarModel ι U) (finiteHaarModel ι V) = haarFamilyHilbertSchmidtDistance ι U V := by
  have he : hilbertSchmidtFamilyDistance
      ((EuclideanSpace.basisFun ι ℂ).map (finiteL2Equiv ι ℂ))
      (finiteHaarModel ι U) (finiteHaarModel ι V) ^ 2 =
      haarFamilyHilbertSchmidtDistance ι U V ^ 2 := by
    rw [haarFamilyHilbertSchmidtDistance, hilbertSchmidtFamilyDistance_sq,
      hilbertSchmidtFamilyDistance_sq]
    simp only [OrthonormalBasis.map_apply, finiteHaarModel, finiteL2Unitary_apply,
      ← map_sub, LinearIsometryEquiv.norm_map]
    rfl
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

/-- Coordinate evaluation on normalized counting L² has norm at most `sqrt(n)`. -/
theorem finiteL2_coordinate_norm_le (f : L2 (finiteProbability ι)) (i : ι) :
    ‖f i‖ ≤ Real.sqrt (Fintype.card ι) * ‖f‖ := by
  let z := (finiteL2Equiv ι ℂ).symm f
  have hz : finiteL2Equiv ι ℂ z = f := (finiteL2Equiv ι ℂ).apply_symm_apply f
  rw [← hz, finiteL2Equiv_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), LinearIsometryEquiv.norm_map]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le z i) (Real.sqrt_nonneg _)

/-- The exact dimension factor in the coordinate Lipschitz bound for the fourth moments. -/
theorem finiteExpression_coordinate_lipschitz (t : StabilityExpression) (i : ι)
    (U V : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) :
    |‖t.eval (finiteHaarModel ι U) i‖ - ‖t.eval (finiteHaarModel ι V) i‖| ≤
      (Real.sqrt (Fintype.card ι) * (t.lipBound : ℝ)) * haarFamilyHilbertSchmidtDistance ι U V := by
  have h := (expression_hilbertSchmidt_bounds t
    ((EuclideanSpace.basisFun ι ℂ).map (finiteL2Equiv ι ℂ))
    (finiteHaarModel ι U) (finiteHaarModel ι V)).2
  rw [finiteHaarModel_hilbertSchmidtDistance] at h
  have hs := (finiteProbability_ae_iff ι).mp
    (Lp.coeFn_sub (t.eval (finiteHaarModel ι U)) (t.eval (finiteHaarModel ι V))) i
  calc
    _ ≤ ‖t.eval (finiteHaarModel ι U) i - t.eval (finiteHaarModel ι V) i‖ :=
      abs_norm_sub_norm_le _ _
    _ = ‖(t.eval (finiteHaarModel ι U) - t.eval (finiteHaarModel ι V)) i‖ := by
      rw [hs]
      rfl
    _ ≤ Real.sqrt (Fintype.card ι) * ‖t.eval (finiteHaarModel ι U) - t.eval (finiteHaarModel ι V)‖ :=
      finiteL2_coordinate_norm_le ι _ i
    _ ≤ Real.sqrt (Fintype.card ι) * ((t.lipBound : ℝ) * haarFamilyHilbertSchmidtDistance ι U V) :=
      mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
    _ = _ := (mul_assoc _ _ _).symm

end OperatorPhaseRetrieval

end
