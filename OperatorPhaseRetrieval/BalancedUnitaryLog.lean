module

public import OperatorPhaseRetrieval.SpectralCoordinates
public import OperatorPhaseRetrieval.BalancedAngles

@[expose] public section

noncomputable section

open NormedSpace

namespace OperatorPhaseRetrieval

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- A finite-dimensional unitary has a selfadjoint logarithm whose operator norm
is at most 3 pi and whose trace has absolute value at most pi. -/
theorem haarUnitary_exists_balanced_log (u : HaarUnitary E) :
    ∃ A : selfAdjoint (E →L[ℂ] E), selfAdjoint.expUnitary A = u ∧
      ‖A‖ ≤ 3 * Real.pi ∧ ‖LinearMap.trace ℂ E (A : E →L[ℂ] E).toLinearMap‖ ≤ Real.pi := by
  classical
  obtain ⟨A, hAu, hAnorm⟩ := haarUnitary_exists_bounded_log E u
  let hA := A.property.isSymmetric
  let b := hA.eigenvectorBasis rfl
  let θ := hA.eigenvalues rfl
  have hAeig (i : Fin (Module.finrank ℂ E)) : (A : E →L[ℂ] E) (b i) = (θ i : ℂ) • b i :=
    hA.apply_eigenvectorBasis rfl i
  have hθ (i : Fin (Module.finrank ℂ E)) : |θ i| ≤ Real.pi := by
    calc
      |θ i| = ‖(A : E →L[ℂ] E) (b i)‖ := by rw [hAeig, norm_smul]; simp
      _ ≤ ‖A‖ := by simpa using (A : E →L[ℂ] E).le_opNorm (b i)
      _ ≤ Real.pi := hAnorm
  obtain ⟨φ, k, hφ, hφnorm, hφsum⟩ := exists_balanced_angles _ θ hθ
  let B : selfAdjoint (E →L[ℂ] E) :=
    ⟨basisDiagonal b (fun i => (φ i : ℂ)), basisDiagonal_isSelfAdjoint b φ⟩
  have hdiag : basisDiagonal b (fun i => (θ i : ℂ)) = (A : E →L[ℂ] E) :=
    basisDiagonal_eq_of_apply_basis b _ _ hAeig
  have hphase (i : Fin (Module.finrank ℂ E)) :
      Complex.exp (Complex.I * (φ i : ℂ)) = Complex.exp (Complex.I * (θ i : ℂ)) := by
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    refine ⟨-k i, ?_⟩
    rw [hφ]
    push_cast
    ring
  refine ⟨B, ?_, ?_, ?_⟩
  · apply Subtype.ext
    change NormedSpace.exp (Complex.I • basisDiagonal b (fun i => (φ i : ℂ))) = (u : E →L[ℂ] E)
    rw [← basisDiagonal_smul, basisDiagonal_exp]
    simp_rw [hphase]
    rw [← basisDiagonal_exp, basisDiagonal_smul, hdiag]
    exact congrArg Subtype.val hAu
  · exact basisDiagonal_norm_le b _ (3 * Real.pi) (by positivity) (by simpa using hφnorm)
  · change ‖LinearMap.trace ℂ E (basisDiagonal b (fun i => (φ i : ℂ))).toLinearMap‖ ≤ Real.pi
    rw [basisDiagonal_trace]
    simpa only [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs] using hφsum

end OperatorPhaseRetrieval

end
