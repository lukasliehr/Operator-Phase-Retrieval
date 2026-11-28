module

public import OperatorPhaseRetrieval.MathlibImports
public import OperatorPhaseRetrieval.CompactPathIntegration

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace OperatorPhaseRetrieval

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [FirstCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Right Haar invariance removes the position on a translated path after averaging. -/
theorem averaged_path_energy_eq (D : G → H →L[ℝ] ℝ) (hD : Continuous D)
    (k : G → H) (hk : Continuous k) (P : G → ℝ → G)
    (hP : Continuous (Function.uncurry P)) :
    (∫ U, ∫ Z, (∫ t in (0 : ℝ)..1, (D (U * P Z t) (k Z)) ^ 2) ∂μ ∂μ) =
      ∫ U, ∫ Z, (D U (k Z)) ^ 2 ∂μ ∂μ := by
  have hc : Continuous (fun p : G × G => ∫ t in (0 : ℝ)..1,
      (D (p.1 * P p.2 t) (k p.2)) ^ 2) := by
    apply compact_unitInterval_integral_continuous
    fun_prop
  rw [integral_integral_swap_of_hasCompactSupport hc (HasCompactSupport.of_compactSpace _)]
  have hz (Z : G) : (∫ U, (∫ t in (0 : ℝ)..1, (D (U * P Z t) (k Z)) ^ 2) ∂μ) =
      ∫ U, (D U (k Z)) ^ 2 ∂μ := by
    rw [compact_unitInterval_integral_swap μ (f := fun U t => (D (U * P Z t) (k Z)) ^ 2) (show Continuous
      (fun p : G × ℝ => (D (p.1 * P Z p.2) (k Z)) ^ 2) by fun_prop)]
    have he (t : ℝ) : (∫ U, (D (U * P Z t) (k Z)) ^ 2 ∂μ) =
        ∫ U, (D U (k Z)) ^ 2 ∂μ :=
      integral_mul_right_eq_self (μ := μ) (fun U => (D U (k Z)) ^ 2) (P Z t)
    simp_rw [he]
    simp
  simp_rw [hz]
  apply integral_integral_swap_of_hasCompactSupport
  · fun_prop
  · exact HasCompactSupport.of_compactSpace _

/-- Average the elementary path energy estimate before using the tangent moment bound. -/
theorem averaged_path_difference_le_energy (F : G → ℝ) (hF : Continuous F)
    (D : G → H →L[ℝ] ℝ) (hD : Continuous D) (k : G → H) (hk : Continuous k)
    (P : G → ℝ → G) (hP : Continuous (Function.uncurry P))
    (hzero : ∀ Z, P Z 0 = 1)
    (hderiv : ∀ U Z t, t ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (fun s => F (U * P Z s)) (D (U * P Z t) (k Z)) t) :
    (∫ U, ∫ Z, (F (U * P Z 1) - F U) ^ 2 ∂μ ∂μ) ≤
      ∫ U, ∫ Z, (D U (k Z)) ^ 2 ∂μ ∂μ := by
  have hp (U Z : G) : (F (U * P Z 1) - F U) ^ 2 ≤
      ∫ t in (0 : ℝ)..1, (D (U * P Z t) (k Z)) ^ 2 := by
    have h := path_squared_difference_le_energy (fun t => F (U * P Z t))
      (fun t => D (U * P Z t) (k Z)) (by fun_prop) (hderiv U Z)
    simpa only [hzero, mul_one] using h
  have hc₁ : Continuous (fun p : G × G => (F (p.1 * P p.2 1) - F p.1) ^ 2) := by fun_prop
  have hc₂ : Continuous (fun p : G × G => ∫ t in (0 : ℝ)..1,
      (D (p.1 * P p.2 t) (k p.2)) ^ 2) := by
    apply compact_unitInterval_integral_continuous
    fun_prop
  rw [← averaged_path_energy_eq μ D hD k hk P hP]
  apply integral_mono
    ((compact_integral_continuous μ hc₁).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((compact_integral_continuous μ hc₂).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  intro U
  apply integral_mono
    ((hc₁.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hc₂.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  exact hp U

/-- A tangent second-moment bound converts path energy into a dimension-dependent increment bound. -/
theorem averaged_path_difference_le_moment (F : G → ℝ) (hF : Continuous F)
    (D : G → H →L[ℝ] ℝ) (hD : Continuous D) (k : G → H) (hk : Continuous k)
    (P : G → ℝ → G) (hP : Continuous (Function.uncurry P))
    (hzero : ∀ Z, P Z 0 = 1)
    (hderiv : ∀ U Z t, t ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (fun s => F (U * P Z s)) (D (U * P Z t) (k Z)) t)
    (K : ℝ) (hmoment : ∀ U, (∫ Z, (D U (k Z)) ^ 2 ∂μ) ≤ K * ‖D U‖ ^ 2) :
    (∫ U, ∫ Z, (F (U * P Z 1) - F U) ^ 2 ∂μ ∂μ) ≤ K * ∫ U, ‖D U‖ ^ 2 ∂μ := by
  apply (averaged_path_difference_le_energy μ F hF D hD k hk P hP hzero hderiv).trans
  rw [← integral_const_mul]
  apply integral_mono
  · exact (compact_integral_continuous μ (show Continuous
      (fun p : G × G => (D p.1 (k p.2)) ^ 2) by fun_prop)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (continuous_const.mul (hD.norm.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact hmoment

variable [μ.IsMulLeftInvariant]

/-- An averaged-path Poincaré principle. The path and tangent direction may be
chosen separately for each endpoint; no measurable choice of logarithms is needed. -/
theorem variance_le_of_averaged_paths (F : G → ℝ) (hF : Continuous F)
    (D : G → H →L[ℝ] ℝ) (hD : Continuous D) (K : ℝ)
    (hpaths : ∀ W : G, ∃ (k : G → H) (P : G → ℝ → G),
      Continuous k ∧ Continuous (Function.uncurry P) ∧
      (∀ Z, P Z 0 = 1) ∧ (∀ Z, P Z 1 = Z * W * Z⁻¹) ∧
      (∀ U Z t, t ∈ Icc (0 : ℝ) 1 →
        HasDerivAt (fun s => F (U * P Z s)) (D (U * P Z t) (k Z)) t) ∧
      (∀ U, (∫ Z, (D U (k Z)) ^ 2 ∂μ) ≤ K * ‖D U‖ ^ 2)) :
    ProbabilityTheory.variance F μ ≤ (K / 2) * ∫ U, ‖D U‖ ^ 2 ∂μ := by
  calc
    _ ≤ (K * ∫ U, ‖D U‖ ^ 2 ∂μ) / 2 := by
      apply variance_le_of_haar_conjugated_increments μ F hF
      intro W
      obtain ⟨k, P, hk, hP, hzero, hone, hderiv, hmoment⟩ := hpaths W
      have h := averaged_path_difference_le_moment μ F hF D hD k hk P hP hzero hderiv K hmoment
      simpa only [hone] using h
    _ = _ := by ring

end OperatorPhaseRetrieval

end
