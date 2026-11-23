import OperatorPhaseRetrieval.FiniteExpressionContinuity

noncomputable section

open MeasureTheory

namespace OperatorPhaseRetrieval

variable (ι : Type*) [Fintype ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Coordinate permutations as genuine Euclidean unitary operators. -/
def permutationHaarUnitary (p : Equiv.Perm ι) : HaarUnitary (EuclideanSpace ℂ ι) :=
  Unitary.linearIsometryEquiv.symm (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ p)

theorem finiteL2Unitary_mul (P Q : HaarUnitary (EuclideanSpace ℂ ι)) (f : L2 (finiteProbability ι)) :
    finiteL2Unitary ι (P * Q) f = finiteL2Unitary ι P (finiteL2Unitary ι Q f) := by
  simp [finiteL2Unitary, map_mul]

theorem finiteL2Unitary_permutation_apply (p : Equiv.Perm ι)
    (f : L2 (finiteProbability ι)) (i : ι) :
    finiteL2Unitary ι (permutationHaarUnitary ι p) f i = f (p.symm i) := by
  let z := (finiteL2Equiv ι ℂ).symm f
  have hz : finiteL2Equiv ι ℂ z = f := (finiteL2Equiv ι ℂ).apply_symm_apply f
  rw [← hz, finiteL2Unitary_apply, finiteL2Equiv_apply, finiteL2Equiv_apply]
  rfl

/-- Simultaneous conjugation of the six Haar matrices. -/
def haarSixConjugate (P : HaarUnitary (EuclideanSpace ℂ ι))
    (U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι) :=
  fun j => P * U j * P⁻¹

omit [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
theorem haarSixConjugate_measurePreserving (P : HaarUnitary (EuclideanSpace ℂ ι)) :
    MeasurePreserving (haarSixConjugate ι P)
      (haarSixProbability ι : Measure _) (haarSixProbability ι : Measure _) := by
  let μ : Measure (HaarUnitary (EuclideanSpace ℂ ι)) :=
    (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure (HaarUnitary (EuclideanSpace ℂ ι)))
  exact measurePreserving_pi (fun _ : Fin 6 => μ) (fun _ : Fin 6 => μ)
    (f := fun (_ : Fin 6) U => P * U * P⁻¹)
    (fun _ => (measurePreserving_mul_right μ P⁻¹).comp (measurePreserving_mul_left μ P))

theorem finiteHaarModel_conjugate_apply (P : HaarUnitary (EuclideanSpace ℂ ι))
    (U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) (j : Fin 6)
    (f : L2 (finiteProbability ι)) :
    finiteHaarModel ι (haarSixConjugate ι P U) j (finiteL2Unitary ι P f) =
      finiteL2Unitary ι P (finiteHaarModel ι U j f) := by
  change finiteL2Unitary ι (P * U j * P⁻¹) (finiteL2Unitary ι P f) = _
  rw [finiteL2Unitary_mul, finiteL2Unitary_mul, finiteL2Unitary_inverse,
    LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem finiteHaarModel_conjugate_inverse_apply (P : HaarUnitary (EuclideanSpace ℂ ι))
    (U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) (j : Fin 6)
    (f : L2 (finiteProbability ι)) :
    (finiteHaarModel ι (haarSixConjugate ι P U) j).symm (finiteL2Unitary ι P f) =
      finiteL2Unitary ι P ((finiteHaarModel ι U j).symm f) := by
  apply (finiteHaarModel ι (haarSixConjugate ι P U) j).injective
  rw [LinearIsometryEquiv.apply_symm_apply, finiteHaarModel_conjugate_apply,
    LinearIsometryEquiv.apply_symm_apply]

theorem finiteL2Unitary_permutation_one (p : Equiv.Perm ι) :
    finiteL2Unitary ι (permutationHaarUnitary ι p) (Lp.const 2 (finiteProbability ι) 1) =
      Lp.const 2 (finiteProbability ι) 1 := by
  have hc := (finiteProbability_ae_iff ι).mp (Lp.coeFn_const 2 (finiteProbability ι) (1 : ℂ))
  apply Lp.ext
  exact Filter.Eventually.of_forall fun i => by
    simp only [finiteL2Unitary_permutation_apply, hc, Function.const_apply]

theorem finiteL2Unitary_permutation_conj (p : Equiv.Perm ι) (f : L2 (finiteProbability ι)) :
    finiteL2Unitary ι (permutationHaarUnitary ι p) (conjugateL2 f) =
      conjugateL2 (finiteL2Unitary ι (permutationHaarUnitary ι p) f) := by
  have h₁ := (finiteProbability_ae_iff ι).mp (conjugateL2_coeFn f)
  have h₂ := (finiteProbability_ae_iff ι).mp
    (conjugateL2_coeFn (finiteL2Unitary ι (permutationHaarUnitary ι p) f))
  apply Lp.ext
  exact Filter.Eventually.of_forall fun i => by
    simp only [finiteL2Unitary_permutation_apply, h₁, h₂]

theorem finiteL2Unitary_permutation_modulus (p : Equiv.Perm ι) (f : L2 (finiteProbability ι)) :
    finiteL2Unitary ι (permutationHaarUnitary ι p) (complexModulusL2 f) =
      complexModulusL2 (finiteL2Unitary ι (permutationHaarUnitary ι p) f) := by
  have h₁ := (finiteProbability_ae_iff ι).mp (complexModulusL2_coeFn f)
  have h₂ := (finiteProbability_ae_iff ι).mp
    (complexModulusL2_coeFn (finiteL2Unitary ι (permutationHaarUnitary ι p) f))
  apply Lp.ext
  exact Filter.Eventually.of_forall fun i => by
    simp only [finiteL2Unitary_permutation_apply, h₁, h₂]

/-- Permutation equivariance holds for every expression, including inverse
operators, conjugation and modulus. -/
theorem finiteExpression_conjugate_permutation (p : Equiv.Perm ι)
    (U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) (t : StabilityExpression) :
    t.eval (finiteHaarModel ι (haarSixConjugate ι (permutationHaarUnitary ι p) U)) =
      finiteL2Unitary ι (permutationHaarUnitary ι p) (t.eval (finiteHaarModel ι U)) := by
  induction t with
  | one => exact (finiteL2Unitary_permutation_one ι p).symm
  | seed =>
    change finiteHaarModel ι (haarSixConjugate ι (permutationHaarUnitary ι p) U) 0
      (Lp.const 2 (finiteProbability ι) 1) = _
    nth_rw 1 [← finiteL2Unitary_permutation_one ι p]
    exact finiteHaarModel_conjugate_apply ι _ U 0 _
  | add s t hs ht => simp only [StabilityExpression.eval, hs, ht, map_add]
  | smul a b t ht => simp only [StabilityExpression.eval, ht, map_smul]
  | conj t ht =>
    simp only [StabilityExpression.eval, ht, finiteL2Unitary_permutation_conj]
  | modulus t ht =>
    simp only [StabilityExpression.eval, ht, finiteL2Unitary_permutation_modulus]
  | apply j inverse t ht =>
    cases inverse with
    | false =>
      simp only [StabilityExpression.eval, unitaryAction, Bool.false_eq_true, ↓reduceIte, ht]
      exact finiteHaarModel_conjugate_apply ι _ U j.succ _
    | true =>
      simp only [StabilityExpression.eval, unitaryAction, ↓reduceIte, ht]
      exact finiteHaarModel_conjugate_inverse_apply ι _ U j.succ _

end OperatorPhaseRetrieval

end
