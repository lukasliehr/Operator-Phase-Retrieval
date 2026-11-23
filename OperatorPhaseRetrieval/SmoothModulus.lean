import OperatorPhaseRetrieval.ExpressionBounds

noncomputable section

namespace OperatorPhaseRetrieval

/-- A smooth, zero-preserving approximation to the complex modulus. -/
def smoothModulus (ε : ℝ) (z : ℂ) : ℂ :=
  ((Real.sqrt (‖z‖ ^ 2 + ε ^ 2) - ε : ℝ) : ℂ)

theorem smoothModulus_zero {ε : ℝ} (hε : 0 ≤ ε) : smoothModulus ε 0 = 0 := by
  simp [smoothModulus, Real.sqrt_sq hε]

theorem sqrt_sq_add_sub_le (r s ε : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    |Real.sqrt (r ^ 2 + ε ^ 2) - Real.sqrt (s ^ 2 + ε ^ 2)| ≤ |r - s| := by
  let R := Real.sqrt (r ^ 2 + ε ^ 2)
  let S := Real.sqrt (s ^ 2 + ε ^ 2)
  have hR : R ^ 2 = r ^ 2 + ε ^ 2 := Real.sq_sqrt (by positivity)
  have hS : S ^ 2 = s ^ 2 + ε ^ 2 := Real.sq_sqrt (by positivity)
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hprod : r*s + ε ^ 2 ≤ R*S := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    calc
      _ ≤ (r ^ 2 + ε ^ 2) * (s ^ 2 + ε ^ 2) := by
        nlinarith [mul_nonneg (sq_nonneg ε) (sq_nonneg (r-s))]
      _ = (R*S) ^ 2 := by rw [mul_pow, hR, hS]
  apply (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
  simp only [sq_abs]
  change (R-S) ^ 2 ≤ (r-s) ^ 2
  nlinarith

theorem smoothModulus_lipschitz (ε : ℝ) : LipschitzWith 1 (smoothModulus ε) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, smoothModulus,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sub_sub_sub_cancel_right]
  exact (sqrt_sq_add_sub_le ‖z‖ ‖w‖ ε (norm_nonneg _) (norm_nonneg _)).trans
    (abs_norm_sub_norm_le z w)

theorem smoothModulus_norm_le {ε : ℝ} (hε : 0 ≤ ε) (z : ℂ) :
    ‖smoothModulus ε z‖ ≤ ‖z‖ := by
  have h := (smoothModulus_lipschitz ε).dist_le_mul z 0
  simpa only [smoothModulus_zero hε, dist_zero_right, NNReal.coe_one, one_mul] using h

theorem smoothModulus_error_le {ε : ℝ} (hε : 0 ≤ ε) (z : ℂ) :
    ‖smoothModulus ε z - (‖z‖ : ℂ)‖ ≤ ε := by
  have hlow : ‖z‖ ≤ Real.sqrt (‖z‖ ^ 2 + ε ^ 2) := by
    apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    nlinarith [sq_nonneg ε]
  have hupp : Real.sqrt (‖z‖ ^ 2 + ε ^ 2) ≤ ‖z‖ + ε := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith [mul_nonneg (norm_nonneg z) hε]
  rw [smoothModulus, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem smoothModulus_contDiff {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ⊤ (smoothModulus ε) := by
  apply Complex.ofRealCLM.contDiff.comp
  apply ContDiff.sub _ contDiff_const
  apply ContDiff.sqrt ((show ContDiff ℝ ⊤ (fun z : ℂ => ‖z‖ ^ 2) from contDiff_norm_sq ℂ).add contDiff_const)
  intro z
  exact ne_of_gt (by nlinarith [sq_nonneg ‖z‖] : 0 < ‖z‖ ^ 2 + ε ^ 2)

end OperatorPhaseRetrieval

end
