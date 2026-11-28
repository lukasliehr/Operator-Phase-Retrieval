module

public import OperatorPhaseRetrieval.HermitianGeometry

@[expose] public section

noncomputable section

namespace OperatorPhaseRetrieval

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- The operator norm is bounded by the Hermitian Hilbert--Schmidt norm. -/
theorem hermitianCoordinateOperator_norm_le (A : hermitianCoordinates ι) :
    ‖hermitianCoordinateOperator ι A‖ ≤ ‖A‖ := by
  obtain ⟨b, a, ha⟩ := exists_selfAdjoint_diagonal
    (hermitianCoordinateOperator ι A) (hermitianCoordinateOperator_isSelfAdjoint ι A)
  have hsq : (∑ i, a i ^ 2) = ‖A‖ ^ 2 := by
    rw [← operatorRealTrace_basisDiagonal_sq b a, ha, hermitianCoordinates_norm_sq]
  rw [← ha]
  apply basisDiagonal_norm_le b _ ‖A‖ (norm_nonneg _)
  intro i
  simp only [Complex.norm_real, Real.norm_eq_abs]
  apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
  rw [sq_abs, ← hsq]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (a j)) (Finset.mem_univ i)

end OperatorPhaseRetrieval

end
