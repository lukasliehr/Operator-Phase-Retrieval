module

public import OperatorPhaseRetrieval.PhaseDistance
public import OperatorPhaseRetrieval.BlockRotation

@[expose] public section

/-! # Two unitary measurements on a two-dimensional space

The finite-dimensional obstruction behind the sharpness of Theorem C is proved constructively.
No spectral decomposition or dimension-counting axiom is required.
-/

noncomputable section

namespace OperatorPhaseRetrieval

theorem exists_phase_equal_add_sub_norm (a b : ℂ) :
    ∃ ω : ℂ, IsPhase ω ∧ ‖a + ω * b‖ = ‖a - ω * b‖ := by
  obtain ⟨ρ, hρ, he⟩ := exists_phase_mul_eq_norm (a * star b)
  let ω := star (Complex.I * ρ)
  have hω : IsPhase ω := by
    simp only [ω, IsPhase, norm_star, norm_mul, Complex.norm_I, one_mul]
    exact hρ
  have hc : a * star (ω * b) = Complex.I * (‖a * star b‖ : ℂ) := by
    simp only [ω, star_mul, star_star]
    calc
      a * (star b * (Complex.I * ρ)) = Complex.I * (ρ * (a * star b)) := by ring
      _ = _ := by rw [he]
  have hr : (a * star (ω * b)).re = 0 := by
    rw [hc]
    simp
  refine ⟨ω, hω, ?_⟩
  have hs : ‖a + ω * b‖ ^ 2 = ‖a - ω * b‖ ^ 2 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_add, Complex.normSq_sub,
      starRingEnd_apply, hr, mul_zero, add_zero, sub_zero]
  nlinarith [norm_nonneg (a + ω * b), norm_nonneg (a - ω * b)]

/-- Equality of the two coordinate magnitudes on the Hilbert space ℂ². -/
def CoordinateModEq (x y : SumL2 ℂ) : Prop := ‖x.fst‖ = ‖y.fst‖ ∧ ‖x.snd‖ = ‖y.snd‖

theorem pair_one_phase_not_related {ω : ℂ} (hω : IsPhase ω) :
    ¬ PhaseRelated (pairL2 (1 : ℂ) ω) (pairL2 (1 : ℂ) (-ω)) := by
  rintro ⟨ζ, _, he⟩
  have h₁ := congrArg (fun x : SumL2 ℂ => x.fst) he
  have h₂ := congrArg (fun x : SumL2 ℂ => x.snd) he
  simp only [pairL2_fst, WithLp.smul_fst, smul_eq_mul, mul_one] at h₁
  simp only [pairL2_snd, WithLp.smul_snd, smul_eq_mul, ← h₁, one_mul] at h₂
  have hz : ω = 0 := by linear_combination -(1 / 2 : ℂ) * h₂
  exact phase_ne_zero hω hz

theorem pair_one_phase_coordinateModEq (ω : ℂ) :
    CoordinateModEq (pairL2 (1 : ℂ) ω) (pairL2 (1 : ℂ) (-ω)) := by
  exact ⟨rfl, (norm_neg ω).symm⟩

theorem pair_linear_fst (T : SumL2 ℂ ≃ₗᵢ[ℂ] SumL2 ℂ) (ω : ℂ) :
    (T (pairL2 (1 : ℂ) ω)).fst =
      (T (pairL2 (1 : ℂ) 0)).fst + ω * (T (pairL2 (0 : ℂ) 1)).fst := by
  have he : pairL2 (1 : ℂ) ω = pairL2 (1 : ℂ) 0 + ω • pairL2 (0 : ℂ) 1 := by
    apply sum_ext <;> simp [WithLp.add_fst, WithLp.add_snd, WithLp.smul_fst, WithLp.smul_snd]
  rw [he, T.map_add, T.map_smul, WithLp.add_fst, WithLp.smul_fst]
  rfl

/-- Identity and any second unitary fail phase retrieval on ℂ². -/
theorem identity_and_unitary_not_phase_retrieval
    (T : SumL2 ℂ ≃ₗᵢ[ℂ] SumL2 ℂ) :
    ∃ x y : SumL2 ℂ, CoordinateModEq x y ∧ CoordinateModEq (T x) (T y) ∧
      ¬ PhaseRelated x y := by
  obtain ⟨ω, hω, he⟩ := exists_phase_equal_add_sub_norm
    (T (pairL2 (1 : ℂ) 0)).fst (T (pairL2 (0 : ℂ) 1)).fst
  let x := pairL2 (1 : ℂ) ω
  let y := pairL2 (1 : ℂ) (-ω)
  have hfirst : ‖(T x).fst‖ = ‖(T y).fst‖ := by
    dsimp [x, y]
    rw [pair_linear_fst T ω, pair_linear_fst T (-ω), neg_mul, ← sub_eq_add_neg]
    exact he
  have hn : ‖x‖ ^ 2 = ‖y‖ ^ 2 := by
    simp only [x, y, WithLp.prod_norm_sq_eq_of_L2, pairL2_fst, pairL2_snd, norm_neg]
  have hx := WithLp.prod_norm_sq_eq_of_L2 (T x)
  have hy := WithLp.prod_norm_sq_eq_of_L2 (T y)
  rw [T.norm_map] at hx hy
  rw [hfirst] at hx
  refine ⟨x, y, pair_one_phase_coordinateModEq ω, ⟨hfirst, ?_⟩,
    pair_one_phase_not_related hω⟩
  nlinarith [norm_nonneg (T x).snd, norm_nonneg (T y).snd]

/-- The obstruction behind the sharpness of Theorem C, for two arbitrary unitaries on ℂ². -/
theorem two_unitaries_not_phase_retrieval
    (B₁ B₂ : SumL2 ℂ ≃ₗᵢ[ℂ] SumL2 ℂ) :
    ∃ x y : SumL2 ℂ, CoordinateModEq (B₁ x) (B₁ y) ∧
      CoordinateModEq (B₂ x) (B₂ y) ∧ ¬ PhaseRelated x y := by
  obtain ⟨x, y, h₁, h₂, hn⟩ := identity_and_unitary_not_phase_retrieval (B₁.symm.trans B₂)
  refine ⟨B₁.symm x, B₁.symm y, by simpa using h₁, h₂, ?_⟩
  rintro ⟨ω, hω, he⟩
  apply hn
  refine ⟨ω, hω, ?_⟩
  simpa only [B₁.map_smul, B₁.apply_symm_apply] using congrArg B₁ he

end OperatorPhaseRetrieval

end
