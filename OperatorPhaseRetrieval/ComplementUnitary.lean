import OperatorPhaseRetrieval.HaarUnitary

noncomputable section

open MeasureTheory Set Metric

namespace OperatorPhaseRetrieval

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

def complementUnitaryExtension (K : Submodule ℂ E) (u : HaarUnitary Kᗮ) : HaarUnitary E :=
  Unitary.linearIsometryEquiv.symm
    (K.orthogonalDecomposition.trans
      ((LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℂ K)
        (Unitary.linearIsometryEquiv u)).trans K.orthogonalDecomposition.symm))

theorem complementUnitaryExtension_apply (K : Submodule ℂ E) (u : HaarUnitary Kᗮ) (x : E) :
    (complementUnitaryExtension K u : E →L[ℂ] E) x =
      (K.orthogonalProjectionOnto x : E) +
        ((u : Kᗮ →L[ℂ] Kᗮ) (Kᗮ.orthogonalProjectionOnto x) : E) := by
  simp [complementUnitaryExtension, Submodule.orthogonalDecomposition_apply]
  rfl

theorem complementUnitaryExtension_fix (K : Submodule ℂ E) (u : HaarUnitary Kᗮ) (x : K) :
    (complementUnitaryExtension K u : E →L[ℂ] E) x = x := by
  rw [complementUnitaryExtension_apply]
  have h0 : Kᗮ.orthogonalProjectionOnto (x : E) = 0 :=
    Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr (by simp)
  rw [h0]
  simp

theorem complementUnitaryExtension_orthogonal (K : Submodule ℂ E) (u : HaarUnitary Kᗮ) (y : Kᗮ) :
    (complementUnitaryExtension K u : E →L[ℂ] E) y = ((u : Kᗮ →L[ℂ] Kᗮ) y : E) := by
  rw [complementUnitaryExtension_apply]
  have h0 : K.orthogonalProjectionOnto (y : E) = 0 :=
    Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr y.property
  rw [h0]
  simp

end OperatorPhaseRetrieval

end
