module

public import OperatorPhaseRetrieval.HaarHermitianSecondMoment

@[expose] public section

noncomputable section

open MeasureTheory NormedSpace
open scoped InnerProductSpace

namespace OperatorPhaseRetrieval

variable (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
theorem hermitianFunctional_identity_sq_le (l : hermitianCoordinates ι →L[ℝ] ℝ) :
    l (hermitianIdentity ι) ^ 2 ≤ ‖l‖ ^ 2 * Fintype.card ι := by
  have h := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg l) (norm_nonneg _))).mpr
    (l.le_opNorm (hermitianIdentity ι))
  simpa only [Real.norm_eq_abs, sq_abs, mul_pow, hermitianIdentity_norm_sq] using h

omit [Nonempty ι] in
/-- A balanced logarithm's Hilbert–Schmidt norm bound. -/
theorem hermitian_balanced_norm_sq_le (A : hermitianCoordinates ι)
    (hA : ‖hermitianCoordinateOperator ι A‖ ≤ 3 * Real.pi) :
    ‖A‖ ^ 2 ≤ 9 * Real.pi ^ 2 * Fintype.card ι := by
  calc
    _ ≤ (Fintype.card ι : ℝ) * ‖hermitianCoordinateOperator ι A‖ ^ 2 :=
      hermitianCoordinates_norm_sq_le ι A
    _ ≤ (Fintype.card ι : ℝ) * (3 * Real.pi) ^ 2 :=
      mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hA)
        (Nat.cast_nonneg _)
    _ = _ := by ring

omit [Nonempty ι] in
/-- The dimension factor needed for both second moments and variance. -/
theorem hermitian_balanced_norm_sq_le_covariance (A : hermitianCoordinates ι)
    (hA : ‖hermitianCoordinateOperator ι A‖ ≤ 3 * Real.pi) (hn : 1 < Fintype.card ι) :
    ‖A‖ ^ 2 ≤ (12 * Real.pi ^ 2 / Fintype.card ι) * ((Fintype.card ι : ℝ) ^ 2 - 1) := by
  have hn2 : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < Fintype.card ι := by linarith
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hnpos).mpr
  have h := mul_le_mul_of_nonneg_right (hermitian_balanced_norm_sq_le ι A hA) hnpos.le
  have h' := mul_nonneg (sq_nonneg Real.pi)
    (show 0 ≤ (Fintype.card ι : ℝ) ^ 2 - 4 by nlinarith)
  nlinarith

theorem hermitianConjugate_secondMoment_le_of_bounds (A : hermitianCoordinates ι)
    (l : hermitianCoordinates ι →L[ℝ] ℝ) (hn : 1 < Fintype.card ι) (C : ℝ)
    (hA : ‖A‖ ^ 2 ≤ C * ((Fintype.card ι : ℝ) ^ 2 - 1))
    (htrace : operatorRealTrace (hermitianCoordinateOperator ι A) ^ 2 ≤ C * Fintype.card ι) :
    (∫ U, (l (hermitianConjugate ι U A)) ^ 2
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) ≤ C * ‖l‖ ^ 2 := by
  have hnR : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < Fintype.card ι := by linarith
  have hden : 0 < (Fintype.card ι : ℝ) ^ 2 - 1 := by nlinarith
  have hcoef : ‖hermitianCenter ι A‖ ^ 2 / ((Fintype.card ι : ℝ) ^ 2 - 1) ≤ C :=
    (div_le_iff₀ hden).mpr ((hermitianCenter_norm_sq_le ι A).trans hA)
  have hproj : 0 ≤ ‖l‖ ^ 2 - l (hermitianIdentity ι) ^ 2 / Fintype.card ι := by
    exact sub_nonneg.mpr ((div_le_iff₀ hnpos).mpr (hermitianFunctional_identity_sq_le ι l))
  have hmean :
      (operatorRealTrace (hermitianCoordinateOperator ι A) / Fintype.card ι *
        l (hermitianIdentity ι)) ^ 2 ≤ C * (l (hermitianIdentity ι) ^ 2 / Fintype.card ι) := by
    calc
      _ = (operatorRealTrace (hermitianCoordinateOperator ι A) ^ 2 / Fintype.card ι) *
          (l (hermitianIdentity ι) ^ 2 / Fintype.card ι) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ((div_le_iff₀ hnpos).mpr htrace)
        (show 0 ≤ l (hermitianIdentity ι) ^ 2 / (Fintype.card ι : ℝ) by positivity)
  rw [hermitianConjugate_functional_secondMoment_general ι A l hn]
  calc
    _ ≤ C * (‖l‖ ^ 2 - l (hermitianIdentity ι) ^ 2 / Fintype.card ι) +
        C * (l (hermitianIdentity ι) ^ 2 / Fintype.card ι) :=
      add_le_add (mul_le_mul_of_nonneg_right hcoef hproj) hmean
    _ = _ := by ring

/-- Balanced logarithm bounds imply a dimension-decaying tangent second moment,
including dimension one. -/
theorem hermitianConjugate_secondMoment_le_balanced (A : hermitianCoordinates ι)
    (hA : ‖hermitianCoordinateOperator ι A‖ ≤ 3 * Real.pi)
    (htrace : |operatorRealTrace (hermitianCoordinateOperator ι A)| ≤ Real.pi)
    (l : hermitianCoordinates ι →L[ℝ] ℝ) :
    (∫ U, (l (hermitianConjugate ι U A)) ^ 2
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) ≤
        (12 * Real.pi ^ 2 / Fintype.card ι) * ‖l‖ ^ 2 := by
  have hnpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hAsq := hermitian_balanced_norm_sq_le ι A hA
  by_cases hn : 1 < Fintype.card ι
  · apply hermitianConjugate_secondMoment_le_of_bounds ι A l hn
    · exact hermitian_balanced_norm_sq_le_covariance ι A hA hn
    · rw [div_mul_cancel₀ _ (ne_of_gt hnpos)]
      have ht := (sq_le_sq₀ (abs_nonneg _) Real.pi_pos.le).mpr htrace
      rw [sq_abs] at ht
      nlinarith [sq_nonneg Real.pi]
  · have hn1 : Fintype.card ι = 1 := by have := Fintype.card_pos (α := ι); omega
    have hp (U : HaarUnitary (EuclideanSpace ℂ ι)) :
        (l (hermitianConjugate ι U A)) ^ 2 ≤ 12 * Real.pi ^ 2 * ‖l‖ ^ 2 := by
      have hl := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg l) (norm_nonneg _))).mpr
        (l.le_opNorm (hermitianConjugate ι U A))
      simp only [Real.norm_eq_abs, sq_abs, mul_pow, hermitianConjugate_norm] at hl
      rw [hn1, Nat.cast_one, mul_one] at hAsq
      have h := mul_le_mul_of_nonneg_left hAsq (sq_nonneg ‖l‖)
      nlinarith [mul_nonneg (sq_nonneg Real.pi) (sq_nonneg ‖l‖)]
    have hi : Integrable (fun U => (l (hermitianConjugate ι U A)) ^ 2)
        (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _) :=
      ((l.continuous.comp (hermitianConjugate_continuous ι A)).pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have h := integral_mono hi (integrable_const (12 * Real.pi ^ 2 * ‖l‖ ^ 2)) hp
    simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
      one_smul, hn1, Nat.cast_one, div_one] using h

end OperatorPhaseRetrieval

end
