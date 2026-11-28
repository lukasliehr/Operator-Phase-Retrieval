module

public import OperatorPhaseRetrieval.HermitianGeometry
public import OperatorPhaseRetrieval.BalancedUnitaryLog

@[expose] public section

noncomputable section

open NormedSpace

namespace OperatorPhaseRetrieval

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

def hermitianExp (A : hermitianCoordinates ι) : HaarUnitary (EuclideanSpace ℂ ι) :=
  selfAdjoint.expUnitary ⟨hermitianCoordinateOperator ι A, hermitianCoordinateOperator_isSelfAdjoint ι A⟩

theorem hermitianExp_coe (A : hermitianCoordinates ι) :
    (hermitianExp ι A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) =
      NormedSpace.exp (Complex.I • hermitianCoordinateOperator ι A) := rfl

@[simp] theorem hermitianExp_zero : hermitianExp ι 0 = 1 := by
  have hz : (⟨hermitianCoordinateOperator ι 0, hermitianCoordinateOperator_isSelfAdjoint ι 0⟩ :
      selfAdjoint (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)) = 0 :=
    Subtype.ext ((hermitianOperatorCLM ι).map_zero)
  exact (congrArg selfAdjoint.expUnitary hz).trans selfAdjoint.expUnitary_zero

theorem hermitianExp_continuous : Continuous (hermitianExp ι) := by
  apply selfAdjoint.continuous_expUnitary.comp
  exact (hermitianOperatorCLM ι).continuous.subtype_mk _

theorem hermitianExp_conjugate (U : HaarUnitary (EuclideanSpace ℂ ι))
    (A : hermitianCoordinates ι) :
    hermitianExp ι (hermitianConjugate ι U A) = U * hermitianExp ι A * U⁻¹ := by
  apply Subtype.ext
  change NormedSpace.exp (Complex.I • hermitianCoordinateOperator ι (hermitianConjugate ι U A)) =
    (Unitary.linearIsometryEquiv U).conjStarAlgEquiv
      (NormedSpace.exp (Complex.I • hermitianCoordinateOperator ι A))
  rw [hermitianConjugate_operator_eq, ← map_smul,
    ← NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) (Unitary.linearIsometryEquiv U).conjStarAlgEquiv
      (StarAlgEquiv.isometry _).continuous _ (by simp [expSeries_radius_eq_top])]

/-- Balanced logarithms in the Hermitian Hilbert--Schmidt tangent space. -/
theorem exists_balanced_hermitian_log (U : HaarUnitary (EuclideanSpace ℂ ι)) :
    ∃ A : hermitianCoordinates ι, hermitianExp ι A = U ∧
      ‖hermitianCoordinateOperator ι A‖ ≤ 3 * Real.pi ∧
      |operatorRealTrace (hermitianCoordinateOperator ι A)| ≤ Real.pi := by
  obtain ⟨B, hB, hnorm, htrace⟩ := haarUnitary_exists_balanced_log (EuclideanSpace ℂ ι) U
  let A : hermitianCoordinates ι := ⟨(hsOperatorEquiv ι).symm (B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι), by
    change IsSelfAdjoint (hsOperatorEquiv ι ((hsOperatorEquiv ι).symm _))
    rw [LinearEquiv.apply_symm_apply]
    exact B.property⟩
  have hA : hermitianCoordinateOperator ι A = B := (hsOperatorEquiv ι).apply_symm_apply _
  refine ⟨A, ?_, ?_, ?_⟩
  · have he : hermitianExp ι A = selfAdjoint.expUnitary B := by
      unfold hermitianExp
      congr 1
      exact Subtype.ext hA
    exact he.trans hB
  · rw [hA]
    exact hnorm
  · rw [hA]
    exact (Complex.abs_re_le_norm _).trans htrace

theorem hermitianExp_smul_coe (A : hermitianCoordinates ι) (t : ℝ) :
    (hermitianExp ι (t • A) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) =
      NormedSpace.exp (t • (Complex.I • hermitianCoordinateOperator ι A)) := by
  rw [hermitianExp_coe]
  change NormedSpace.exp (Complex.I • hermitianOperatorCLM ι (t • A)) = _
  rw [map_smul, smul_comm]
  rfl

/-- The operator-valued unitary path has the expected right-translated tangent. -/
theorem hermitianExp_hasDerivAt (A : hermitianCoordinates ι) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (hermitianExp ι (s • A) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι))
      ((hermitianExp ι (t • A) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) *
        (Complex.I • hermitianCoordinateOperator ι A)) t := by
  simp only [hermitianExp_smul_coe]
  exact hasDerivAt_exp_smul_const (Complex.I • hermitianCoordinateOperator ι A) t

end OperatorPhaseRetrieval

end
