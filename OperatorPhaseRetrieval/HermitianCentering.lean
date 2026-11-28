module

public import OperatorPhaseRetrieval.HermitianCoordinates

@[expose] public section

noncomputable section

open NormedSpace
open scoped InnerProductSpace

namespace OperatorPhaseRetrieval

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- The identity as a Hermitian Hilbert--Schmidt vector. -/
def hermitianIdentity : hermitianCoordinates ι :=
  ⟨(hsOperatorEquiv ι).symm 1, by
    change IsSelfAdjoint (hsOperatorEquiv ι ((hsOperatorEquiv ι).symm 1))
    rw [LinearEquiv.apply_symm_apply]
    exact IsSelfAdjoint.one _⟩

@[simp]
theorem hermitianIdentity_operator : hermitianCoordinateOperator ι (hermitianIdentity ι) = 1 :=
  (hsOperatorEquiv ι).apply_symm_apply 1

omit [DecidableEq ι] in
theorem operatorRealTrace_one :
    operatorRealTrace (1 : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) = Fintype.card ι := by
  simp [operatorRealTrace, LinearMap.trace_one]

theorem hermitianIdentity_norm_sq : ‖hermitianIdentity ι‖ ^ 2 = (Fintype.card ι : ℝ) := by
  rw [← hermitianCoordinates_norm_sq, hermitianIdentity_operator, one_pow, operatorRealTrace_one]

theorem hermitianIdentity_inner (A : hermitianCoordinates ι) :
    inner ℝ (hermitianIdentity ι) A = operatorRealTrace (hermitianCoordinateOperator ι A) := by
  rw [hermitianCoordinates_inner_trace, hermitianIdentity_operator, one_mul]

def hermitianCenter (A : hermitianCoordinates ι) : hermitianCoordinates ι :=
  A - (operatorRealTrace (hermitianCoordinateOperator ι A) / Fintype.card ι) • hermitianIdentity ι

variable [Nonempty ι]

theorem hermitianCenter_trace (A : hermitianCoordinates ι) :
    operatorRealTrace (hermitianCoordinateOperator ι (hermitianCenter ι A)) = 0 := by
  rw [← hermitianIdentity_inner]
  unfold hermitianCenter
  rw [inner_sub_right, real_inner_smul_right (hermitianIdentity ι) (hermitianIdentity ι), hermitianIdentity_inner, hermitianIdentity_inner,
    hermitianIdentity_operator, operatorRealTrace_one]
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  ring

theorem hermitianCenter_norm_sq (A : hermitianCoordinates ι) :
    ‖hermitianCenter ι A‖ ^ 2 = ‖A‖ ^ 2 -
      (operatorRealTrace (hermitianCoordinateOperator ι A)) ^ 2 / Fintype.card ι := by
  unfold hermitianCenter
  rw [norm_sub_sq_real, real_inner_smul_right A (hermitianIdentity ι), real_inner_comm (hermitianIdentity ι) A, hermitianIdentity_inner,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hermitianIdentity_norm_sq]
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  ring

theorem hermitianCenter_norm_sq_le (A : hermitianCoordinates ι) :
    ‖hermitianCenter ι A‖ ^ 2 ≤ ‖A‖ ^ 2 := by
  rw [hermitianCenter_norm_sq]
  exact sub_le_self _ (by positivity)

end OperatorPhaseRetrieval

end
