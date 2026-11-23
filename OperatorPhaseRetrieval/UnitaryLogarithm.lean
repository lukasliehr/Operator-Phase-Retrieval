import OperatorPhaseRetrieval.HaarUnitary
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected

noncomputable section

open Complex NormedSpace selfAdjoint Unitary

namespace OperatorPhaseRetrieval

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- In finite dimension the argument is continuous on every unitary spectrum,
including spectra containing the branch-cut point -1. -/
theorem haarUnitary_arg_continuousOn (u : HaarUnitary E) :
    ContinuousOn Complex.arg (spectrum ℂ (u : E →L[ℂ] E)) := by
  rw [ContinuousLinearMap.spectrum_eq]
  exact (Module.End.finite_spectrum (u : E →ₗ[ℂ] E)).continuousOn Complex.arg

/-- Every finite-dimensional unitary has a selfadjoint logarithm of norm at most pi. -/
theorem haarUnitary_exp_arg (u : HaarUnitary E) :
    selfAdjoint.expUnitary (Unitary.argSelfAdjoint u) = u := by
  have : ContinuousOn arg (spectrum ℂ (u : E →L[ℂ] E)) := haarUnitary_arg_continuousOn E u
  apply Subtype.ext
  rw [expUnitary_coe, argSelfAdjoint_coe, ← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ),
    ← cfc_comp_smul .., ← cfc_comp' ..]
  conv_rhs => rw [← cfc_id' ℂ (u : E →L[ℂ] E)]
  refine cfc_congr fun y hy ↦ ?_
  have hy₁ : ‖y‖ = 1 := spectrum.norm_eq_one_of_unitary u.2 hy
  have : I * y.arg = log y :=
    Complex.ext (by simp [log_re, spectrum.norm_eq_one_of_unitary u.2 hy]) (by simp [log_im])
  simpa [← exp_eq_exp_ℂ, this] using exp_log (by aesop)

theorem haarUnitary_exists_bounded_log (u : HaarUnitary E) :
    ∃ A : selfAdjoint (E →L[ℂ] E), selfAdjoint.expUnitary A = u ∧ ‖A‖ ≤ Real.pi :=
  ⟨Unitary.argSelfAdjoint u, haarUnitary_exp_arg E u, Unitary.norm_argSelfAdjoint_le_pi u⟩

end OperatorPhaseRetrieval

end
