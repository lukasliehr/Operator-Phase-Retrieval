module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Function.Holder
public import OperatorPhaseRetrieval.L2
public import OperatorPhaseRetrieval.Projection

@[expose] public section

/-! Fourier shifts and the quadratic forms determined by the two magnitudes. -/
noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace ComplexConjugate ENNReal
namespace OperatorPhaseRetrieval.TwoUnitary

abbrev μ := AddCircle.haarAddCircle (T := (1 : ℝ))
abbrev H := L2 μ
abbrev Op := H →L[ℂ] H
abbrev basis := fourierBasis (T := (1 : ℝ))

def entry (A : Op) (a b : ℤ) := inner ℂ (basis a) (A (basis b))
def quad (A : Op) (h : H) := inner ℂ h (A h)

theorem basis_ext {A B : Op} (h : ∀ b : ℤ, A (basis b) = B (basis b)) : A = B := by
  apply ContinuousLinearMap.ext_on (s := Set.range basis)
  · intro x
    change x ∈ (Submodule.span ℂ (Set.range ⇑basis)).topologicalClosure
    rw [basis.dense_span]
    trivial
  · rintro _ ⟨b,rfl⟩
    exact h b

def permBasis (r : Equiv.Perm ℤ) : HilbertBasis ℤ ℂ H :=
  HilbertBasis.mk (basis.orthonormal.comp r r.injective) (by
    rw [Set.range_comp, r.surjective.range_eq, Set.image_univ, basis.dense_span])

def permEquiv (r : Equiv.Perm ℤ) : H ≃ₗᵢ[ℂ] H :=
  basis.repr.trans (permBasis r).repr.symm

def permOp (r : Equiv.Perm ℤ) : Op := (permEquiv r : Op)

@[simp] theorem permOp_basis (r : Equiv.Perm ℤ) (b : ℤ) :
    permOp r (basis b) = basis (r b) := by
  change (permBasis r).repr.symm (basis.repr (basis b)) = _
  rw [basis.repr_self, HilbertBasis.repr_symm_single]
  simp [permBasis]

theorem permOp_unitary (r : Equiv.Perm ℤ) : IsUnitary (permOp r) := by
  constructor <;> ext x : 1 <;> simp [permOp, mul_apply_eq_comp]

def shift (N : ℤ) : Op := permOp (Equiv.addLeft N)
@[simp] theorem shift_basis (N b : ℤ) : shift N (basis b) = basis (N + b) :=
  permOp_basis _ _

theorem shift_unitary (N : ℤ) : IsUnitary (shift N) := permOp_unitary _

theorem shift_add (m n : ℤ) : shift (m+n) = shift m * shift n := by
  apply basis_ext
  intro b
  change shift (m+n) (basis b) = shift m (shift n (basis b))
  simp only [shift_basis, add_assoc]

theorem shift_nat_mul (m : ℕ) (d : ℤ) : shift (m*d) = (shift d)^m := by
  induction m with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, pow_zero]
    apply basis_ext
    intro b
    simp only [shift_basis, zero_add, one_apply_eq_self]
  | succ m ih => rw [Nat.cast_succ, add_mul, one_mul, shift_add, ih, pow_succ]

def multiplier (N : ℤ) : Op :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL μ ∞ 2 2 (fourierLp ∞ N)

theorem multiplier_ae (N : ℤ) (h : H) :
    (multiplier N h : UnitAddCircle → ℂ) =ᵐ[μ] fun x => fourier N x * h x := by
  filter_upwards [ContinuousLinearMap.coeFn_holder (μ := μ) (r := 2)
    (ContinuousLinearMap.mul ℂ ℂ) (fourierLp ∞ N) h, coeFn_fourierLp (T := 1) ∞ N]
    with x hx he
  exact hx.trans (congrArg (· * h x) he)

theorem shift_ae (N : ℤ) (h : H) :
    (shift N h : UnitAddCircle → ℂ) =ᵐ[μ] fun x => fourier N x * h x := by
  suffices he : shift N = multiplier N by rw [he]; exact multiplier_ae N h
  apply basis_ext
  intro b
  rw [shift_basis]
  apply Lp.ext
  filter_upwards [multiplier_ae N (basis b), coeFn_fourierLp (T := 1) 2 b,
    coeFn_fourierLp (T := 1) 2 (N+b)] with x hm hb hs
  rw [coe_fourierBasis] at hm ⊢
  rw [hm, hb, hs, fourier_add]

theorem shift_quad_eq (N : ℤ) {f g : H} (h : ModEq f g) :
    quad (shift N) f = quad (shift N) g := by
  unfold quad
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [shift_ae N f, shift_ae N g, h] with x hf hg hx
  rw [hf,hg]
  simp only [RCLike.inner_apply, starRingEnd_apply]
  have hs : star (f x) * f x = star (g x) * g x := by
    change (starRingEnd ℂ) _ * _ = (starRingEnd ℂ) _ * _
    rw [← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hx]
  linear_combination fourier N x * hs

def readout (V : Op) (N : ℤ) (z : ℂ) : Op := z⁻¹ • (star V * shift N * V - shift N)

theorem readout_quad_eq (V : Op) (N : ℤ) (z : ℂ) {f g : H}
    (h : ModEq f g) (hV : ModEq (V f) (V g)) :
    quad (readout V N z) f = quad (readout V N z) g := by
  have formula (h : H) : quad (readout V N z) h =
      z⁻¹ * (quad (shift N) (V h) - quad (shift N) h) := by
    simp [quad, readout, mul_apply_eq_comp, inner_smul_right, inner_sub_right,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  rw [formula, formula, shift_quad_eq N h, shift_quad_eq N hV]

end OperatorPhaseRetrieval.TwoUnitary
