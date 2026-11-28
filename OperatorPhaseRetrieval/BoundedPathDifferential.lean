module

public import OperatorPhaseRetrieval.MathlibImports
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

@[expose] public section

noncomputable section

open scoped NNReal

namespace OperatorPhaseRetrieval

set_option backward.isDefEq.respectTransparency false

variable {G H E F : Type*} [TopologicalSpace G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous differential along a specified family of paths, with a uniform bound. -/
def HasBoundedPathDifferential (path : G → H → ℝ → G) (f : G → E) (L : ℝ) : Prop :=
  Continuous f ∧ ∃ D : G → H →L[ℝ] E, Continuous D ∧
    (∀ U A t, HasDerivAt (fun s => f (path U A s)) (D (path U A t) A) t) ∧
    ∀ U A, ‖D U A‖ ≤ L * ‖A‖

namespace HasBoundedPathDifferential

variable {path : G → H → ℝ → G} {f g : G → E} {L M : ℝ}

theorem mono (hf : HasBoundedPathDifferential path f L) (hLM : L ≤ M) :
    HasBoundedPathDifferential path f M := by
  obtain ⟨hfc, D, hDc, hDd, hDb⟩ := hf
  exact ⟨hfc, D, hDc, hDd, fun U A =>
    (hDb U A).trans (mul_le_mul_of_nonneg_right hLM (norm_nonneg _))⟩

theorem const (x : E) : HasBoundedPathDifferential path (fun _ => x) 0 := by
  refine ⟨continuous_const, fun _ => 0, continuous_const, ?_, ?_⟩
  · intro U A t
    simpa using hasDerivAt_const t x
  · simp

theorem add (hf : HasBoundedPathDifferential path f L)
    (hg : HasBoundedPathDifferential path g M) :
    HasBoundedPathDifferential path (fun U => f U + g U) (L + M) := by
  obtain ⟨hfc, D, hDc, hDd, hDb⟩ := hf
  obtain ⟨hgc, B, hBc, hBd, hBb⟩ := hg
  refine ⟨hfc.add hgc, fun U => D U + B U, hDc.add hBc, ?_, ?_⟩
  · intro U A t
    exact (hDd U A t).add (hBd U A t)
  · intro U A
    exact (norm_add_le _ _).trans (by simpa [add_mul] using add_le_add (hDb U A) (hBb U A))

theorem clm_comp (hf : HasBoundedPathDifferential path f L) (T : E →L[ℝ] F) :
    HasBoundedPathDifferential path (fun U => T (f U)) (‖T‖ * L) := by
  obtain ⟨hfc, D, hDc, hDd, hDb⟩ := hf
  refine ⟨T.continuous.comp hfc, fun U => T.comp (D U), ?_, ?_, ?_⟩
  · exact continuous_const.clm_comp hDc
  · intro U A t
    exact T.hasFDerivAt.comp_hasDerivAt t (hDd U A t)
  · intro U A
    exact (T.le_opNorm (D U A)).trans (by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left (hDb U A) (norm_nonneg T))

theorem smooth_comp (hf : HasBoundedPathDifferential path f L)
    (φ : E → F) (hφ : ContDiff ℝ ⊤ φ) (K : ℝ≥0) (hlip : LipschitzWith K φ) :
    HasBoundedPathDifferential path (fun U => φ (f U)) (K * L) := by
  obtain ⟨hfc, D, hDc, hDd, hDb⟩ := hf
  refine ⟨hφ.continuous.comp hfc, fun U => (fderiv ℝ φ (f U)).comp (D U), ?_, ?_, ?_⟩
  · exact ((hφ.continuous_fderiv (by simp)).comp hfc).clm_comp hDc
  · intro U A t
    exact ((hφ.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t (hDd U A t)
  · intro U A
    calc
      _ ≤ ‖fderiv ℝ φ (f U)‖ * ‖D U A‖ := (fderiv ℝ φ (f U)).le_opNorm _
      _ ≤ (K : ℝ) * ‖D U A‖ := mul_le_mul_of_nonneg_right
        (norm_fderiv_le_of_lipschitz ℝ hlip) (norm_nonneg _)
      _ ≤ _ := by simpa [mul_assoc] using mul_le_mul_of_nonneg_left (hDb U A) K.coe_nonneg

theorem clm_apply {T : G → E →L[ℝ] F} {K R : ℝ}
    (hT : HasBoundedPathDifferential path T K) (hf : HasBoundedPathDifferential path f L)
    (hTb : ∀ U, ‖T U‖ ≤ 1) (hfb : ∀ U, ‖f U‖ ≤ R) (hK : 0 ≤ K) :
    HasBoundedPathDifferential path (fun U => T U (f U)) (K * R + L) := by
  obtain ⟨hTc, B, hBc, hBd, hBb⟩ := hT
  obtain ⟨hfc, D, hDc, hDd, hDb⟩ := hf
  let D' : G → H →L[ℝ] F := fun U =>
    (ContinuousLinearMap.apply ℝ F (f U)).comp (B U) + (T U).comp (D U)
  refine ⟨hTc.clm_apply hfc, D', ?_, ?_, ?_⟩
  · dsimp [D']
    exact (((ContinuousLinearMap.apply ℝ F).continuous.comp hfc).clm_comp hBc).add
      (hTc.clm_comp hDc)
  · intro U A t
    exact (hBd U A t).clm_apply (hDd U A t)
  · intro U A
    change ‖B U A (f U) + T U (D U A)‖ ≤ _
    calc
      _ ≤ ‖B U A (f U)‖ + ‖T U (D U A)‖ := norm_add_le _ _
      _ ≤ ‖B U A‖ * ‖f U‖ + ‖T U‖ * ‖D U A‖ :=
        add_le_add ((B U A).le_opNorm _) ((T U).le_opNorm _)
      _ ≤ (K * ‖A‖) * R + 1 * (L * ‖A‖) := add_le_add
        (mul_le_mul (hBb U A) (hfb U) (norm_nonneg _) (mul_nonneg hK (norm_nonneg _)))
        (mul_le_mul (hTb U) (hDb U A) (norm_nonneg _) (by norm_num))
      _ = _ := by ring

end HasBoundedPathDifferential
end OperatorPhaseRetrieval

end
