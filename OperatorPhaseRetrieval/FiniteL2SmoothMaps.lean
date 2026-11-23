import OperatorPhaseRetrieval.EuclideanCoordinateMaps
import OperatorPhaseRetrieval.FiniteExpressionContinuity

noncomputable section

open MeasureTheory

namespace OperatorPhaseRetrieval

set_option backward.isDefEq.respectTransparency false

variable (ι : Type*) [Fintype ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- A scalar map on normalized finite L² is conjugate to a Euclidean coordinate map,
with the normalization factors made explicit. -/
theorem finiteL2_compLp_eq_coordinates (ψ : ℂ → ℂ) (hψ : LipschitzWith 1 ψ) (hzero : ψ 0 = 0)
    (f : L2 (finiteProbability ι)) :
    hψ.compLp hzero f = finiteL2Equiv ι ℂ
      ((Real.sqrt (Fintype.card ι))⁻¹ • euclideanCoordinateMap ι ψ
        (Real.sqrt (Fintype.card ι) • (finiteL2Equiv ι ℂ).symm f)) := by
  have hs : Real.sqrt (Fintype.card ι) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)).ne'
  have he (i : ι) : Real.sqrt (Fintype.card ι) • ((finiteL2Equiv ι ℂ).symm f) i = f i := by
    simpa only [(finiteL2Equiv ι ℂ).apply_symm_apply] using
      (finiteL2Equiv_apply ι ℂ ((finiteL2Equiv ι ℂ).symm f) i).symm
  apply Lp.ext
  apply (finiteProbability_ae_iff ι).mpr
  intro i
  rw [(finiteProbability_ae_iff ι).mp (hψ.coeFn_compLp hzero f) i, finiteL2Equiv_apply]
  change ψ (f i) = Real.sqrt (Fintype.card ι) •
    ((Real.sqrt (Fintype.card ι))⁻¹ • ψ (Real.sqrt (Fintype.card ι) • ((finiteL2Equiv ι ℂ).symm f) i))
  rw [smul_smul, mul_inv_cancel₀ hs, one_smul, he]

/-- Smooth scalar maps act smoothly on finite normalized L². -/
theorem finiteL2_compLp_contDiff (ψ : ℂ → ℂ) (hψ : LipschitzWith 1 ψ) (hzero : ψ 0 = 0)
    (hsmooth : ContDiff ℝ ⊤ ψ) :
    ContDiff ℝ ⊤ (fun f : L2 (finiteProbability ι) => hψ.compLp hzero f) := by
  have he : (fun f : L2 (finiteProbability ι) => hψ.compLp hzero f) =
      fun f => finiteL2Equiv ι ℂ ((Real.sqrt (Fintype.card ι))⁻¹ • euclideanCoordinateMap ι ψ
        (Real.sqrt (Fintype.card ι) • (finiteL2Equiv ι ℂ).symm f)) :=
    funext (finiteL2_compLp_eq_coordinates ι ψ hψ hzero)
  rw [he]
  have h₁ : ContDiff ℝ ⊤ (fun f : L2 (finiteProbability ι) =>
      Real.sqrt (Fintype.card ι) • (finiteL2Equiv ι ℂ).symm f) :=
    (((finiteL2Equiv ι ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).contDiff).const_smul _
  have h₂ : ContDiff ℝ ⊤ (fun f : L2 (finiteProbability ι) =>
      (Real.sqrt (Fintype.card ι))⁻¹ • euclideanCoordinateMap ι ψ
        (Real.sqrt (Fintype.card ι) • (finiteL2Equiv ι ℂ).symm f)) :=
    ((euclideanCoordinateMap_contDiff ι ψ hsmooth).comp h₁).const_smul _
  exact ((finiteL2Equiv ι ℂ).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp h₂

theorem finiteL2_conjugate_contDiff :
    ContDiff ℝ ⊤ (conjugateL2 : L2 (finiteProbability ι) → L2 (finiteProbability ι)) :=
  finiteL2_compLp_contDiff ι _ Complex.isometry_conj.lipschitz (map_zero _)
    Complex.conjCLE.contDiff

end OperatorPhaseRetrieval

end
