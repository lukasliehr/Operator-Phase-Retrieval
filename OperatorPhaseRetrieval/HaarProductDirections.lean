module

public import OperatorPhaseRetrieval.HaarHermitianVariance
public import OperatorPhaseRetrieval.IndependentSecondMoments

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory NormedSpace
open scoped InnerProductSpace

namespace OperatorPhaseRetrieval

set_option synthInstance.maxHeartbeats 100000

variable (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The tangent space of six unitary factors with the product Hilbert--Schmidt norm. -/
abbrev HermitianSix := PiLp 2 (fun _ : Fin 6 => hermitianCoordinates ι)

instance hermitianSix_normedSpace : NormedSpace ℝ (HermitianSix ι) :=
  PiLp.normedSpace 2 ℝ (fun _ : Fin 6 => hermitianCoordinates ι)

instance hermitianSix_innerProductSpace : InnerProductSpace ℝ (HermitianSix ι) :=
  PiLp.innerProductSpace (fun _ : Fin 6 => hermitianCoordinates ι)

def hermitianSixConjugate (U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι))
    (A : HermitianSix ι) : HermitianSix ι :=
  WithLp.toLp 2 (fun j => hermitianConjugate ι (U j) (A j))

omit [Nonempty ι] in
theorem hermitianSixConjugate_continuous (A : HermitianSix ι) :
    Continuous (fun U => hermitianSixConjugate ι U A) := by
  apply (PiLp.continuous_toLp 2 _).comp
  exact continuous_pi (fun j => (hermitianConjugate_continuous ι (A j)).comp (continuous_apply j))

/-- The six-factor tangent moment has the same dimension-decaying bound: independence
controls the trace-zero directions and Cauchy--Schwarz controls the scalar directions. -/
theorem hermitianSixConjugate_secondMoment_le (A : HermitianSix ι)
    (hA : ∀ j, ‖hermitianCoordinateOperator ι (A j)‖ ≤ 3 * Real.pi)
    (htrace : ∀ j, |operatorRealTrace (hermitianCoordinateOperator ι (A j))| ≤ Real.pi)
    (l : HermitianSix ι →L[ℝ] ℝ) (hn : 1 < Fintype.card ι) :
    (∫ U, (l (hermitianSixConjugate ι U A)) ^ 2 ∂(haarSixProbability ι : Measure _)) ≤
      (12 * Real.pi ^ 2 / Fintype.card ι) * ‖l‖ ^ 2 := by
  let B := (InnerProductSpace.toDual ℝ (HermitianSix ι)).symm l
  have hBnorm : ‖B‖ = ‖l‖ := (InnerProductSpace.toDual ℝ (HermitianSix ι)).symm.norm_map l
  have hB (x : HermitianSix ι) : l x = inner ℝ B x :=
    (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := HermitianSix ι) (x := x) (y := l)).symm
  let f := fun j : Fin 6 => InnerProductSpace.toDual ℝ (hermitianCoordinates ι) (B j)
  have hf (j : Fin 6) : ‖f j‖ = ‖B j‖ := (InnerProductSpace.toDual ℝ (hermitianCoordinates ι)).norm_map _
  let X := fun j U => f j (hermitianConjugate ι U (A j))
  let μ : Fin 6 → Measure (HaarUnitary (EuclideanSpace ℂ ι)) :=
    fun _ => (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)
  have hX (j : Fin 6) : MemLp (X j) 2 (μ j) :=
    ((f j).continuous.comp (hermitianConjugate_continuous ι (A j))).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he (U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) :
      l (hermitianSixConjugate ι U A) = ∑ j, X j (U j) := by
    rw [hB, PiLp.inner_apply]
    rfl
  simp_rw [he]
  have h := secondMoment_sum_pi_le μ X hX
    (fun j => operatorRealTrace (hermitianCoordinateOperator ι (A j)))
    (fun j => f j (hermitianIdentity ι)) (fun j => ‖B j‖ ^ 2)
    (Fintype.card ι) (12 * Real.pi ^ 2 / Fintype.card ι)
    (by exact_mod_cast Fintype.card_pos) ?_ ?_ ?_
  · change (∫ U, (∑ j, X j (U j)) ^ 2 ∂Measure.pi μ) ≤ _
    simpa only [← PiLp.norm_sq_eq_of_L2, hBnorm] using h
  · intro j
    exact hermitianConjugate_functional_mean ι (A j) (f j)
  · intro j
    simpa only [hf] using hermitianConjugate_variance_le_balanced ι (A j) (hA j) (f j) hn
  · have hn0 : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    rw [div_mul_cancel₀ _ hn0]
    calc
      _ ≤ ∑ _j : Fin 6, Real.pi ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) Real.pi_pos.le).mpr (htrace j)
      _ ≤ _ := by
        norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
        nlinarith [sq_nonneg Real.pi]

end OperatorPhaseRetrieval

end
