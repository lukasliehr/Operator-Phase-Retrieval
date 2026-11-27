import OperatorPhaseRetrieval.HaarProductPoincare

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace

namespace OperatorPhaseRetrieval

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

variable (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The fourth-moment consequence of Poincaré for a smooth complex coordinate.
Its continuous tangent derivative has the `sqrt(n) L` bound and its second
moment has the dimension-independent bound `R²`. -/
theorem haarSix_smooth_fourthMoment_le (hn : 1 < Fintype.card ι)
    (F : (Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) → ℂ) (hF : Continuous F)
    (D : (Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) → HermitianSix ι →L[ℝ] ℂ)
    (hD : Continuous D)
    (hderiv : ∀ U A t, t ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (fun s => F (U * hermitianSixExp ι (s • A)))
        (D (U * hermitianSixExp ι (t • A)) A) t)
    (R L : ℝ) (hL : 0 ≤ L)
    (hsecond : (∫ U, ‖F U‖ ^ 2 ∂(haarSixProbability ι : Measure _)) ≤ R ^ 2)
    (hbound : ∀ U, ‖D U‖ ≤ Real.sqrt (Fintype.card ι) * L) :
    (∫ U, ‖F U‖ ^ 4 ∂(haarSixProbability ι : Measure _)) ≤
      R ^ 4 + 240 * R ^ 2 * L ^ 2 := by
  let μ : Measure (Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) := (haarSixProbability ι : Measure _)
  let D₂ : (Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) → HermitianSix ι →L[ℝ] ℝ :=
    fun U => (2 : ℝ) • (innerSL ℝ (F U)).comp (D U)
  have hc₂ : Continuous D₂ := by dsimp [D₂]; fun_prop
  have hd₂ U A t (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s => ‖F (U * hermitianSixExp ι (s • A))‖ ^ 2)
        (D₂ (U * hermitianSixExp ι (t • A)) A) t := by
    change HasDerivAt _ (2 * inner ℝ (F (U * hermitianSixExp ι (t • A)))
      (D (U * hermitianSixExp ι (t • A)) A)) t
    exact (hderiv U A t ht).norm_sq
  have hp := haarSix_poincare_sixty ι hn (fun U => ‖F U‖ ^ 2) (hF.norm.pow 2) D₂ hc₂ hd₂
  have hpoint U : ‖D₂ U‖ ^ 2 ≤ (4 * (Fintype.card ι : ℝ) * L ^ 2) * ‖F U‖ ^ 2 := by
    have hd : ‖D₂ U‖ ≤ 2 * ‖F U‖ * (Real.sqrt (Fintype.card ι) * L) := by
      calc
        _ = 2 * ‖(innerSL ℝ (F U)).comp (D U)‖ := by
          have h := norm_smul (2 : ℝ) ((innerSL ℝ (F U)).comp (D U))
          simpa only [Real.norm_ofNat] using h
        _ ≤ 2 * (‖innerSL ℝ (F U)‖ * ‖D U‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (by norm_num)
        _ ≤ _ := by rw [innerSL_apply_norm]; nlinarith [mul_le_mul_of_nonneg_left (hbound U) (norm_nonneg (F U))]
    have hs := (sq_le_sq₀ (norm_nonneg (D₂ U))
      (show 0 ≤ 2 * ‖F U‖ * (Real.sqrt (Fintype.card ι) * L) by positivity)).mpr hd
    calc
      _ ≤ (2 * ‖F U‖ * (Real.sqrt (Fintype.card ι) * L)) ^ 2 := hs
      _ = _ := by rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; ring
  have hint : (∫ U, ‖D₂ U‖ ^ 2 ∂μ) ≤
      (4 * (Fintype.card ι : ℝ) * L ^ 2) * ∫ U, ‖F U‖ ^ 2 ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono (f := fun U => ‖D₂ U‖ ^ 2)
      (g := fun U => (4 * (Fintype.card ι : ℝ) * L ^ 2) * ‖F U‖ ^ 2)
      ((hc₂.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((continuous_const.mul (hF.norm.pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    exact hpoint
  have hn0 : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hv : variance (fun U => ‖F U‖ ^ 2) μ ≤ 240 * L ^ 2 * ∫ U, ‖F U‖ ^ 2 ∂μ := by
    apply hp.trans
    apply (mul_le_mul_of_nonneg_left hint (by positivity : 0 ≤ 60 / (Fintype.card ι : ℝ))).trans_eq
    field_simp
    ring
  have hmem : MemLp (fun U => ‖F U‖ ^ 2) 2 μ :=
    (hF.norm.pow 2).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [variance_eq_sub hmem] at hv
  simp only [Pi.pow_apply, ← pow_mul] at hv
  norm_num only at hv
  have hm0 : 0 ≤ ∫ U, ‖F U‖ ^ 2 ∂μ := integral_nonneg (fun U => sq_nonneg _)
  have hmsq := (sq_le_sq₀ hm0 (sq_nonneg R)).mpr hsecond
  have hm := mul_le_mul_of_nonneg_left hsecond (by positivity : 0 ≤ 240 * L ^ 2)
  nlinarith

theorem haarSix_smooth_fourthMoment_bound (hn : 1 < Fintype.card ι)
    (F : (Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) → ℂ) (hF : Continuous F)
    (D : (Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) → HermitianSix ι →L[ℝ] ℂ)
    (hD : Continuous D)
    (hderiv : ∀ U A t, t ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (fun s => F (U * hermitianSixExp ι (s • A)))
        (D (U * hermitianSixExp ι (t • A)) A) t)
    (R L : ℝ) (hL : 0 ≤ L)
    (hsecond : (∫ U, ‖F U‖ ^ 2 ∂(haarSixProbability ι : Measure _)) ≤ R ^ 2)
    (hbound : ∀ U, ‖D U‖ ≤ Real.sqrt (Fintype.card ι) * L) :
    (∫ U, ‖F U‖ ^ 4 ∂(haarSixProbability ι : Measure _)) ≤ 8 * R ^ 4 + 2304 * L ^ 4 :=
  (haarSix_smooth_fourthMoment_le ι hn F hF D hD hderiv R L hL hsecond hbound).trans
    (fourth_moment_constant_of_poincare R L)

end OperatorPhaseRetrieval

end
