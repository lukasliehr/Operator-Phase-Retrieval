import OperatorPhaseRetrieval.L2

/-!
# Distance modulo a constant complex phase

The distance `d(f, g) = inf_{|ω|=1} ‖f - ωg‖` modulo a global phase.
We prove that the infimum is attained and that `d(f, g)² = ‖f‖² + ‖g‖² - 2|⟨f, g⟩|`.
-/

noncomputable section

open scoped InnerProductSpace

namespace OperatorPhaseRetrieval

theorem exists_phase_mul_eq_norm (z : ℂ) :
    ∃ ω : ℂ, IsPhase ω ∧ ω * z = (‖z‖ : ℂ) := by
  obtain ⟨ω, hω, he⟩ := Complex.exists_norm_eq_mul_self z
  exact ⟨ω, hω, he.symm⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The infimum over all constant unimodular phases. -/
def phaseDistance (f g : H) : ℝ :=
  sInf {r : ℝ | ∃ ω : ℂ, IsPhase ω ∧ r = ‖f - ω • g‖}

theorem phaseDistance_nonneg (f g : H) : 0 ≤ phaseDistance f g := by
  apply le_csInf
  · exact ⟨‖f - (1 : ℂ) • g‖, 1, norm_one, rfl⟩
  · rintro r ⟨ω, _, rfl⟩
    exact norm_nonneg _

theorem phaseDistance_le (f g : H) {ω : ℂ} (hω : IsPhase ω) :
    phaseDistance f g ≤ ‖f - ω • g‖ := by
  apply csInf_le
  · exact ⟨0, by rintro r ⟨ζ, _, rfl⟩; exact norm_nonneg _⟩
  · exact ⟨ω, hω, rfl⟩

theorem phase_aligned_minimum (f g : H) :
    ∃ ω : ℂ, IsPhase ω ∧
      ⟪f, ω • g⟫_ℂ = (‖⟪f, g⟫_ℂ‖ : ℂ) ∧
      ∀ ζ : ℂ, IsPhase ζ → ‖f - ω • g‖ ≤ ‖f - ζ • g‖ := by
  obtain ⟨ω, hω, he⟩ := exists_phase_mul_eq_norm ⟪f, g⟫_ℂ
  refine ⟨ω, hω, by simpa only [inner_smul_right] using he, ?_⟩
  intro ζ hζ
  have ha := norm_sub_sq (𝕜 := ℂ) f (ω • g)
  have hb := norm_sub_sq (𝕜 := ℂ) f (ζ • g)
  have hc : (ζ * ⟪f, g⟫_ℂ).re ≤ ‖⟪f, g⟫_ℂ‖ := by
    simpa only [norm_mul, show ‖ζ‖ = 1 from hζ, one_mul] using
      Complex.re_le_norm (ζ * ⟪f, g⟫_ℂ)
  simp only [norm_smul, show ‖ω‖ = 1 from hω, show ‖ζ‖ = 1 from hζ,
    one_mul, inner_smul_right, he, RCLike.re_eq_complex_re, Complex.ofReal_re] at ha hb
  nlinarith [norm_nonneg (f - ω • g), norm_nonneg (f - ζ • g)]

theorem phaseDistance_attained (f g : H) :
    ∃ ω : ℂ, IsPhase ω ∧ phaseDistance f g = ‖f - ω • g‖ ∧
      ⟪f, ω • g⟫_ℂ = (‖⟪f, g⟫_ℂ‖ : ℂ) := by
  obtain ⟨ω, hω, he, hmin⟩ := phase_aligned_minimum f g
  refine ⟨ω, hω, le_antisymm (phaseDistance_le f g hω) ?_, he⟩
  apply le_csInf
  · exact ⟨‖f - ω • g‖, ω, hω, rfl⟩
  · rintro r ⟨ζ, hζ, rfl⟩
    exact hmin ζ hζ

/-- The formula `d(f, g)² = ‖f‖² + ‖g‖² - 2|⟨f, g⟩|`, valid in every complex inner product space. -/
theorem phaseDistance_sq (f g : H) :
    phaseDistance f g ^ 2 = ‖f‖ ^ 2 + ‖g‖ ^ 2 - 2 * ‖⟪f, g⟫_ℂ‖ := by
  obtain ⟨ω, hω, hd, he⟩ := phaseDistance_attained f g
  rw [hd, norm_sub_sq (𝕜 := ℂ), he]
  simp only [norm_smul, show ‖ω‖ = 1 from hω, one_mul,
    RCLike.re_eq_complex_re, Complex.ofReal_re]
  ring

theorem phaseDistance_map {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (W : H →ₗᵢ[ℂ] G) (f g : H) : phaseDistance (W f) (W g) = phaseDistance f g := by
  have he : ∀ ω : ℂ, ‖W f - ω • W g‖ = ‖f - ω • g‖ := by
    intro ω
    rw [← W.map_smul, ← W.map_sub, W.norm_map]
  simp only [phaseDistance, he]

theorem phaseDistance_eq_sqrt (f g : H) :
    phaseDistance f g = Real.sqrt (‖f‖ ^ 2 + ‖g‖ ^ 2 - 2 * ‖⟪f, g⟫_ℂ‖) := by
  rw [← phaseDistance_sq, Real.sqrt_sq (phaseDistance_nonneg f g)]

theorem continuous_phaseDistance : Continuous (fun p : H × H => phaseDistance p.1 p.2) := by
  simp_rw [phaseDistance_eq_sqrt]
  exact (((continuous_fst.norm.pow 2).add (continuous_snd.norm.pow 2)).sub
    (continuous_const.mul (continuous_fst.inner continuous_snd).norm)).sqrt

theorem phaseDistance_triangle (f g h : H) :
    phaseDistance f h ≤ phaseDistance f g + phaseDistance g h := by
  obtain ⟨ω, hω, hfg, _⟩ := phaseDistance_attained f g
  obtain ⟨ζ, hζ, hgh, _⟩ := phaseDistance_attained g h
  have hωζ : IsPhase (ω * ζ) := by
    change ‖ω * ζ‖ = 1
    rw [norm_mul, show ‖ω‖ = 1 from hω, show ‖ζ‖ = 1 from hζ, one_mul]
  calc
    phaseDistance f h ≤ ‖f - (ω * ζ) • h‖ := phaseDistance_le f h hωζ
    _ = ‖(f - ω • g) + ω • (g - ζ • h)‖ := by congr 1; module
    _ ≤ ‖f - ω • g‖ + ‖ω • (g - ζ • h)‖ := norm_add_le _ _
    _ = phaseDistance f g + phaseDistance g h := by
      rw [norm_smul, show ‖ω‖ = 1 from hω, one_mul, hfg, hgh]

theorem phaseDistance_eq_zero_iff (f g : H) : phaseDistance f g = 0 ↔ PhaseRelated f g := by
  constructor
  · intro hz
    obtain ⟨ω, hω, hd, _⟩ := phaseDistance_attained f g
    have hf : f = ω • g := sub_eq_zero.mp (norm_eq_zero.mp (hd.symm.trans hz))
    refine ⟨star ω, by simpa only [IsPhase, norm_star] using hω, ?_⟩
    rw [hf, smul_smul, mul_comm (star ω), phase_mul_conj hω, one_smul]
  · rintro ⟨ω, hω, rfl⟩
    apply le_antisymm _ (phaseDistance_nonneg f (ω • f))
    have hs : IsPhase (star ω) := by simpa only [IsPhase, norm_star] using hω
    simpa only [smul_smul, mul_comm (star ω), phase_mul_conj hω, one_smul,
      sub_self, norm_zero] using phaseDistance_le f (ω • f) hs

theorem phaseDistance_symm (f g : H) : phaseDistance f g = phaseDistance g f := by
  have he : ‖⟪f, g⟫_ℂ‖ = ‖⟪g, f⟫_ℂ‖ := by
    rw [← inner_conj_symm f g]
    exact norm_star _
  rw [phaseDistance_eq_sqrt, phaseDistance_eq_sqrt, he, add_comm (‖f‖ ^ 2)]

end OperatorPhaseRetrieval

end
