import OperatorPhaseRetrieval.StabilityLimits

/-!
# Unitary extension from a dense family with preserved Gram matrix

This supplies the operator-extension step of the limit construction, including
well-definedness on linear relations and surjectivity. The families and their
Gram identities are explicit inputs; the finite models must provide them.
-/

noncomputable section

open Filter Set
open scoped InnerProductSpace Topology

namespace OperatorPhaseRetrieval

variable {ι H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Equal Gram matrices give equal norms for every finite complex linear
combination, so all linear relations are respected. -/
theorem linearCombination_norm_eq_of_gram (x : ι → H) (y : ι → K)
    (hGram : ∀ i j, ⟪x i, x j⟫_ℂ = ⟪y i, y j⟫_ℂ) (c : ι →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ x c‖ = ‖Finsupp.linearCombination ℂ y c‖ := by
  have he : ⟪Finsupp.linearCombination ℂ x c, Finsupp.linearCombination ℂ x c⟫_ℂ =
      ⟪Finsupp.linearCombination ℂ y c, Finsupp.linearCombination ℂ y c⟫_ℂ := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, hGram]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hr := congrArg Complex.re he
  simpa only [← RCLike.re_eq_complex_re, inner_self_eq_norm_sq] using hr

variable [CompleteSpace K]

/-- The image of a densely spanning family with the same Gram matrix defines
an actual complex-linear isometry on the complete target. -/
theorem exists_isometry_of_gram (x : ι → H) (y : ι → K)
    (hx : Dense (Submodule.span ℂ (Set.range x) : Set H))
    (hGram : ∀ i j, ⟪x i, x j⟫_ℂ = ⟪y i, y j⟫_ℂ) :
    ∃ U : H →ₗᵢ[ℂ] K, ∀ i, U (x i) = y i := by
  let e := Finsupp.linearCombination ℂ x
  let f := Finsupp.linearCombination ℂ y
  have he : DenseRange e := by
    change Dense (LinearMap.range e : Set H)
    simpa only [e, Finsupp.range_linearCombination] using hx
  have hnorm (c : ι →₀ ℂ) : ‖f c‖ = ‖e c‖ :=
    (linearCombination_norm_eq_of_gram x y hGram c).symm
  have hbound : ∃ C : ℝ, ∀ c, ‖f c‖ ≤ C * ‖e c‖ :=
    ⟨1, fun c => by simp [hnorm c]⟩
  let F : H →L[ℂ] K := f.extendOfNorm e
  have hFe c : F (e c) = f c := LinearMap.extendOfNorm_eq he hbound c
  have hFnorm (v : H) : ‖F v‖ = ‖v‖ := by
    refine he.induction ?_ (isClosed_eq F.continuous.norm continuous_norm) v
    rintro _ ⟨c, rfl⟩
    rw [hFe c, hnorm c]
  let U : H →ₗᵢ[ℂ] K := { F.toLinearMap with norm_map' := hFnorm }
  refine ⟨U, fun i => ?_⟩
  change F (x i) = y i
  have h := hFe (Finsupp.single i 1)
  simpa only [e, f, Finsupp.linearCombination_single, one_smul] using h

variable [CompleteSpace H]

/-- Dense source and image spans upgrade the isometry to a surjective
complex-linear unitary. No injectivity of the indexing family is needed. -/
theorem exists_unitary_of_gram (x : ι → H) (y : ι → K)
    (hx : Dense (Submodule.span ℂ (Set.range x) : Set H))
    (hy : Dense (Submodule.span ℂ (Set.range y) : Set K))
    (hGram : ∀ i j, ⟪x i, x j⟫_ℂ = ⟪y i, y j⟫_ℂ) :
    ∃ U : H ≃ₗᵢ[ℂ] K, ∀ i, U (x i) = y i := by
  obtain ⟨U, hU⟩ := exists_isometry_of_gram x y hx hGram
  have hspan : Submodule.span ℂ (Set.range y) ≤ U.toLinearMap.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨x i, hU i⟩
  have hd : Dense (Set.range U) := hy.mono hspan
  have hc : IsClosed (Set.range U) := U.isometry.isClosedEmbedding.isClosed_range
  have hu : Set.range U = Set.univ := by rw [← hc.closure_eq, hd.closure_eq]
  refine ⟨LinearIsometryEquiv.ofSurjective U (Set.range_eq_univ.mp hu), ?_⟩
  exact hU

/-- For the formal-expression construction, inverse expressions ensure that
the image family spans densely, even before an inverse operator is defined. -/
theorem exists_unitary_of_gram_of_range_subset (x y : ι → H)
    (hx : Dense (Submodule.span ℂ (Set.range x) : Set H))
    (hxy : Set.range x ⊆ Set.range y)
    (hGram : ∀ i j, ⟪x i, x j⟫_ℂ = ⟪y i, y j⟫_ℂ) :
    ∃ U : H ≃ₗᵢ[ℂ] H, ∀ i, U (x i) = y i :=
  exists_unitary_of_gram x y hx (hx.mono (Submodule.span_mono hxy)) hGram

end OperatorPhaseRetrieval

end
