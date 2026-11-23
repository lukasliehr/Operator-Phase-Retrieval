import Mathlib.Analysis.Complex.Basic

noncomputable section

namespace OperatorPhaseRetrieval

/-- Fourth-power polarization with the four coordinate phases. -/
theorem complex_four_phase_fourth (a b : ℂ) :
    ‖a+b‖ ^ 4 + ‖a-b‖ ^ 4 + ‖a+Complex.I*b‖ ^ 4 + ‖a-Complex.I*b‖ ^ 4 =
      4 * ‖a‖ ^ 4 + 4 * ‖b‖ ^ 4 + 16 * ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  have h2 (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using (Complex.normSq_eq_norm_sq z).symm
  have h4 (z : ℂ) : ‖z‖ ^ 4 = (z.re ^ 2 + z.im ^ 2) ^ 2 := by
    rw [show 4 = 2*2 by norm_num, pow_mul, h2]
  simp only [h4, h2, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

/-- The Poincaré mixed-moment bound implies the fourth-moment bound of Lemma 4.8. -/
theorem fourth_moment_constant_of_poincare (R L : ℝ) :
    R ^ 4 + 240 * R ^ 2 * L ^ 2 ≤ 8 * R ^ 4 + 2304 * L ^ 4 := by
  nlinarith [sq_nonneg ((5/2 : ℝ) * R ^ 2 - 48 * L ^ 2), sq_nonneg (R ^ 2)]

end OperatorPhaseRetrieval

end
