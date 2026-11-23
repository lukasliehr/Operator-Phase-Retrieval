import OperatorPhaseRetrieval.HaarProductDirections
import OperatorPhaseRetrieval.HaarUnitaryPoincare

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace OperatorPhaseRetrieval

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

def hermitianSixExp (A : HermitianSix ι) : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι) :=
  fun j => hermitianExp ι (A j)

theorem hermitianSixExp_continuous : Continuous (hermitianSixExp ι) :=
  continuous_pi (fun j => (hermitianExp_continuous ι).comp (PiLp.continuous_apply 2 _ j))

@[simp] theorem hermitianSixExp_zero : hermitianSixExp ι 0 = 1 := by
  funext j
  exact hermitianExp_zero ι

theorem hermitianSixExp_conjugate (U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι))
    (A : HermitianSix ι) :
    hermitianSixExp ι (hermitianSixConjugate ι U A) = U * hermitianSixExp ι A * U⁻¹ := by
  funext j
  exact hermitianExp_conjugate ι (U j) (A j)

theorem exists_balanced_hermitianSix_log (W : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) :
    ∃ A : HermitianSix ι, hermitianSixExp ι A = W ∧
      (∀ j, ‖hermitianCoordinateOperator ι (A j)‖ ≤ 3 * Real.pi) ∧
      (∀ j, |operatorRealTrace (hermitianCoordinateOperator ι (A j))| ≤ Real.pi) := by
  choose A hA hnorm htrace using fun j => exists_balanced_hermitian_log ι (W j)
  exact ⟨WithLp.toLp 2 A, funext hA, hnorm, htrace⟩

variable [Nonempty ι]

/-- Poincaré inequality for six independent Haar unitary matrices, in dimension at least two. -/
theorem haarSix_poincare (hn : 1 < Fintype.card ι)
    (F : (Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) → ℝ) (hF : Continuous F)
    (D : (Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) → HermitianSix ι →L[ℝ] ℝ)
    (hD : Continuous D)
    (hderiv : ∀ U A t, t ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (fun s => F (U * hermitianSixExp ι (s • A)))
        (D (U * hermitianSixExp ι (t • A)) A) t) :
    variance F (haarSixProbability ι : Measure _) ≤
      (6 * Real.pi ^ 2 / Fintype.card ι) *
        ∫ U, ‖D U‖ ^ 2 ∂(haarSixProbability ι : Measure _) := by
  let μ : Measure (Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) := (haarSixProbability ι : Measure _)
  have : μ.IsMulLeftInvariant := by dsimp [μ, haarSixProbability]; infer_instance
  have : μ.IsMulRightInvariant := by dsimp [μ, haarSixProbability]; infer_instance
  calc
    _ ≤ ((12 * Real.pi ^ 2 / Fintype.card ι) / 2) * ∫ U, ‖D U‖ ^ 2 ∂μ := by
      apply variance_le_of_averaged_paths (H := HermitianSix ι) μ F hF D hD
      intro W
      obtain ⟨A, hA, hnorm, htrace⟩ := exists_balanced_hermitianSix_log ι W
      refine ⟨fun Z => hermitianSixConjugate ι Z A,
        fun Z t => hermitianSixExp ι (t • hermitianSixConjugate ι Z A),
        hermitianSixConjugate_continuous ι A, ?_, ?_, ?_, ?_, ?_⟩
      · exact (hermitianSixExp_continuous ι).comp
          (continuous_snd.smul ((hermitianSixConjugate_continuous ι A).comp continuous_fst))
      · intro Z
        simp only [zero_smul, hermitianSixExp_zero]
      · intro Z
        simp only [one_smul, hermitianSixExp_conjugate, hA]
      · intro U Z t ht
        exact hderiv U (hermitianSixConjugate ι Z A) t ht
      · intro U
        exact hermitianSixConjugate_secondMoment_le ι A hnorm htrace (D U) hn
    _ = _ := by ring

/-- The convenient rational constant used for expression fourth moments. -/
theorem haarSix_poincare_sixty (hn : 1 < Fintype.card ι)
    (F : (Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) → ℝ) (hF : Continuous F)
    (D : (Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) → HermitianSix ι →L[ℝ] ℝ)
    (hD : Continuous D)
    (hderiv : ∀ U A t, t ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (fun s => F (U * hermitianSixExp ι (s • A)))
        (D (U * hermitianSixExp ι (t • A)) A) t) :
    variance F (haarSixProbability ι : Measure _) ≤
      (60 / Fintype.card ι) * ∫ U, ‖D U‖ ^ 2 ∂(haarSixProbability ι : Measure _) := by
  apply (haarSix_poincare ι hn F hF D hD hderiv).trans
  apply mul_le_mul_of_nonneg_right _ (integral_nonneg fun U => sq_nonneg _)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  nlinarith [Real.pi_pos, Real.pi_lt_d2]

end OperatorPhaseRetrieval

end
