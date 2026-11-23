import OperatorPhaseRetrieval.Stability
import Mathlib.Tactic.DeriveCountable

/-!
# Countable expressions and dimension-independent bounds

The syntax in Section 4.3 includes both each measurement and its inverse.
The estimates below hold on every probability space. In particular their
constants do not depend on the size of a normalized finite counting space.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace OperatorPhaseRetrieval

/-- Rational complex coefficients, encoded without introducing a new scalar field. -/
def rationalComplex (a b : ℚ) : ℂ := (a : ℂ) + (b : ℂ) * Complex.I

/-- The formal expressions used in the limiting construction. -/
inductive StabilityExpression
  | one
  | seed
  | add (s t : StabilityExpression)
  | smul (a b : ℚ) (t : StabilityExpression)
  | conj (t : StabilityExpression)
  | modulus (t : StabilityExpression)
  | apply (j : Fin 5) (inverse : Bool) (t : StabilityExpression)
  deriving Countable

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def conjugateL2 (f : L2 μ) : L2 μ :=
  Complex.isometry_conj.lipschitz.compLp (map_zero _) f

theorem lipschitz_complex_modulus : LipschitzWith 1 (fun z : ℂ => (‖z‖ : ℂ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact abs_norm_sub_norm_le z w

def complexModulusL2 (f : L2 μ) : L2 μ :=
  lipschitz_complex_modulus.compLp (by simp) f

theorem conjugateL2_coeFn (f : L2 μ) :
    (conjugateL2 f : X → ℂ) =ᵐ[μ] (fun x => star (f x)) :=
  Complex.isometry_conj.lipschitz.coeFn_compLp (map_zero _) f

theorem complexModulusL2_coeFn (f : L2 μ) :
    (complexModulusL2 f : X → ℂ) =ᵐ[μ] (fun x => (‖f x‖ : ℂ)) :=
  lipschitz_complex_modulus.coeFn_compLp (by simp) f

theorem conjugateL2_norm_le (f : L2 μ) : ‖conjugateL2 f‖ ≤ ‖f‖ := by
  simpa [conjugateL2] using Complex.isometry_conj.lipschitz.norm_compLp_le (map_zero _) f

theorem complexModulusL2_norm_le (f : L2 μ) : ‖complexModulusL2 f‖ ≤ ‖f‖ := by
  simpa [complexModulusL2] using lipschitz_complex_modulus.norm_compLp_le (by simp) f

theorem conjugateL2_sub_le (f g : L2 μ) : ‖conjugateL2 f - conjugateL2 g‖ ≤ ‖f - g‖ := by
  simpa [conjugateL2] using
    Complex.isometry_conj.lipschitz.norm_compLp_sub_le (map_zero _) f g

theorem complexModulusL2_sub_le (f g : L2 μ) :
    ‖complexModulusL2 f - complexModulusL2 g‖ ≤ ‖f - g‖ := by
  simpa [complexModulusL2] using lipschitz_complex_modulus.norm_compLp_sub_le (by simp) f g

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Operator-norm distance of six unitary operators. This is bounded by their
product Hilbert--Schmidt distance in finite dimensions. -/
def unitaryFamilyDistance (U V : Fin 6 → H ≃ₗᵢ[ℂ] H) : ℝ :=
  ‖fun j => (U j).toLinearIsometry.toContinuousLinearMap - (V j).toLinearIsometry.toContinuousLinearMap‖

theorem unitaryFamilyDistance_nonneg (U V : Fin 6 → H ≃ₗᵢ[ℂ] H) :
    0 ≤ unitaryFamilyDistance U V := norm_nonneg _

theorem unitaryFamilyDistance_symm (U V : Fin 6 → H ≃ₗᵢ[ℂ] H) :
    unitaryFamilyDistance U V = unitaryFamilyDistance V U := by
  unfold unitaryFamilyDistance
  rw [show (fun j => (U j).toLinearIsometry.toContinuousLinearMap - (V j).toLinearIsometry.toContinuousLinearMap) =
    -(fun j => (V j).toLinearIsometry.toContinuousLinearMap - (U j).toLinearIsometry.toContinuousLinearMap) by
      funext j; simp]
  exact norm_neg _

theorem unitaryFamily_apply_sub_le (U V : Fin 6 → H ≃ₗᵢ[ℂ] H) (j : Fin 6) (f : H) :
    ‖U j f - V j f‖ ≤ unitaryFamilyDistance U V * ‖f‖ := by
  calc
    _ ≤ ‖(U j).toLinearIsometry.toContinuousLinearMap - (V j).toLinearIsometry.toContinuousLinearMap‖ * ‖f‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (norm_le_pi_norm
      (fun k => (U k).toLinearIsometry.toContinuousLinearMap -
        (V k).toLinearIsometry.toContinuousLinearMap) j) (norm_nonneg f)

theorem unitaryFamily_inverse_sub_le (U V : Fin 6 → H ≃ₗᵢ[ℂ] H) (j : Fin 6) (f : H) :
    ‖(U j).symm f - (V j).symm f‖ ≤ unitaryFamilyDistance U V * ‖f‖ := by
  have he : ‖(U j).symm f - (V j).symm f‖ =
      ‖V j ((V j).symm f) - U j ((V j).symm f)‖ := by
    rw [← (U j).norm_map, map_sub, (U j).apply_symm_apply, (V j).apply_symm_apply]
  rw [he]
  simpa only [unitaryFamilyDistance_symm V U, (V j).symm.norm_map] using
    unitaryFamily_apply_sub_le V U j ((V j).symm f)

def unitaryAction (U : Fin 6 → H ≃ₗᵢ[ℂ] H) (j : Fin 5) (inverse : Bool) : H ≃ₗᵢ[ℂ] H :=
  if inverse then (U j.succ).symm else U j.succ

theorem unitaryAction_sub_le (U V : Fin 6 → H ≃ₗᵢ[ℂ] H) (j : Fin 5)
    (inverse : Bool) (f g : H) :
    ‖unitaryAction U j inverse f - unitaryAction V j inverse g‖ ≤
      ‖f - g‖ + unitaryFamilyDistance U V * ‖g‖ := by
  calc
    _ ≤ ‖unitaryAction U j inverse f - unitaryAction U j inverse g‖ +
        ‖unitaryAction U j inverse g - unitaryAction V j inverse g‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by
      rw [← map_sub, (unitaryAction U j inverse).norm_map]
      apply add_le_add_right
      cases inverse
      · exact unitaryFamily_apply_sub_le U V j.succ g
      · exact unitaryFamily_inverse_sub_le U V j.succ g

namespace StabilityExpression

/-- The radius and Lipschitz bounds are determined by syntax alone. -/
def radius : StabilityExpression → ℝ≥0
  | .one | .seed => 1
  | .add s t => s.radius + t.radius
  | .smul a b t => ‖rationalComplex a b‖₊ * t.radius
  | .conj t | .modulus t | .apply _ _ t => t.radius

def lipBound : StabilityExpression → ℝ≥0
  | .one => 0
  | .seed => 1
  | .add s t => s.lipBound + t.lipBound
  | .smul a b t => ‖rationalComplex a b‖₊ * t.lipBound
  | .conj t | .modulus t => t.lipBound
  | .apply _ _ t => t.lipBound + t.radius

variable [IsProbabilityMeasure μ]

def eval (U : Fin 6 → L2 μ ≃ₗᵢ[ℂ] L2 μ) : StabilityExpression → L2 μ
  | .one => Lp.const 2 μ 1
  | .seed => U 0 (Lp.const 2 μ 1)
  | .add s t => eval U s + eval U t
  | .smul a b t => rationalComplex a b • eval U t
  | .conj t => conjugateL2 (eval U t)
  | .modulus t => complexModulusL2 (eval U t)
  | .apply j inverse t => unitaryAction U j inverse (eval U t)

theorem eval_norm_le (U : Fin 6 → L2 μ ≃ₗᵢ[ℂ] L2 μ) (t : StabilityExpression) :
    ‖t.eval U‖ ≤ t.radius := by
  induction t with
  | one => simp [eval, radius, Lp.norm_const]
  | seed => simp [eval, radius, Lp.norm_const]
  | add s t hs ht =>
    exact (norm_add_le _ _).trans (by simpa [radius] using add_le_add hs ht)
  | smul a b t ht =>
    simpa [eval, radius, norm_smul] using mul_le_mul_of_nonneg_left ht (norm_nonneg (rationalComplex a b))
  | conj t ht => exact (conjugateL2_norm_le _).trans ht
  | modulus t ht => exact (complexModulusL2_norm_le _).trans ht
  | apply j inverse t ht => simpa [eval, radius] using ht

theorem eval_sub_le (U V : Fin 6 → L2 μ ≃ₗᵢ[ℂ] L2 μ) (t : StabilityExpression) :
    ‖t.eval U - t.eval V‖ ≤ t.lipBound * unitaryFamilyDistance U V := by
  induction t with
  | one => simp [eval, lipBound]
  | seed => simpa [eval, lipBound, Lp.norm_const] using
      unitaryFamily_apply_sub_le U V 0 (Lp.const 2 μ 1)
  | add s t hs ht =>
    simp only [eval, lipBound, NNReal.coe_add]
    calc
      _ = ‖(s.eval U - s.eval V) + (t.eval U - t.eval V)‖ := by congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (by simpa [add_mul] using add_le_add hs ht)
  | smul a b t ht =>
    simp only [eval, lipBound, ← smul_sub, norm_smul, NNReal.coe_mul, coe_nnnorm]
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left ht (norm_nonneg (rationalComplex a b))
  | conj t ht => exact (conjugateL2_sub_le _ _).trans ht
  | modulus t ht => exact (complexModulusL2_sub_le _ _).trans ht
  | apply j inverse t ht =>
    exact (unitaryAction_sub_le U V j inverse _ _).trans (by
      have hb := mul_le_mul_of_nonneg_left (t.eval_norm_le V) (unitaryFamilyDistance_nonneg U V)
      change _ ≤ ((t.lipBound : ℝ) + t.radius) * unitaryFamilyDistance U V
      nlinarith)

/-- Strictly positive dimension-independent bounds for each formal expression. -/
theorem exists_positive_bounds (t : StabilityExpression) :
    ∃ R L : ℝ, 0 < R ∧ 0 < L ∧
      ∀ (X : Type*) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
        (U V : Fin 6 → L2 μ ≃ₗᵢ[ℂ] L2 μ),
        ‖t.eval U‖ ≤ R ∧ ‖t.eval U - t.eval V‖ ≤ L * unitaryFamilyDistance U V := by
  refine ⟨t.radius + 1, t.lipBound + 1, by positivity, by positivity, ?_⟩
  intro X _ μ _ U V
  constructor
  · exact (t.eval_norm_le U).trans (by linarith)
  · exact (t.eval_sub_le U V).trans (mul_le_mul_of_nonneg_right (by linarith)
      (unitaryFamilyDistance_nonneg U V))

end StabilityExpression

end OperatorPhaseRetrieval

end
