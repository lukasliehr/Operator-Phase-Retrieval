import OperatorPhaseRetrieval.OrthogonalReduction
import OperatorPhaseRetrieval.Stability

/-! # From normalized orthogonal pairs to the full stability estimate -/

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace OperatorPhaseRetrieval

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem magnitude_real_smul (a : ℝ) (f : L2 μ) :
    magnitude ((a : ℂ) • f) = |a| • magnitude f := by
  apply Lp.ext
  filter_upwards [magnitude_coeFn ((a : ℂ) • f),
    Lp.coeFn_smul (a : ℂ) f, Lp.coeFn_smul |a| (magnitude f), magnitude_coeFn f]
    with x h₁ h₂ h₃ h₄
  simp only [h₁, h₂, h₃, h₄, Pi.smul_apply, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, smul_eq_mul]

theorem magnitudeDistance_mono_ae {u v f g : L2 μ}
    (h : ∀ᵐ x ∂μ, |‖u x‖ - ‖v x‖| ≤ |‖f x‖ - ‖g x‖|) :
    ‖magnitude u - magnitude v‖ ≤ ‖magnitude f - magnitude g‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [h, Lp.coeFn_sub (magnitude u) (magnitude v),
    Lp.coeFn_sub (magnitude f) (magnitude g),
    magnitude_coeFn u, magnitude_coeFn v, magnitude_coeFn f, magnitude_coeFn g]
    with x hx h₁ h₂ hu hv hf hg
  simpa only [h₁, h₂, Pi.sub_apply, hu, hv, hf, hg, Real.norm_eq_abs] using hx

variable {ι : Type*} [Fintype ι]

theorem measurementDistance_real_smul (U : ι → L2 μ ≃ₗᵢ[ℂ] L2 μ) (a : ℝ) (f g : L2 μ) :
    measurementDistance U ((a : ℂ) • f) ((a : ℂ) • g) = |a| * measurementDistance U f g := by
  unfold measurementDistance
  simp only [map_smul, magnitude_real_smul, ← smul_sub]
  rw [show (fun j => |a| • (magnitude (U j f) - magnitude (U j g))) =
    |a| • (fun j => magnitude (U j f) - magnitude (U j g)) from rfl, norm_smul,
    Real.norm_eq_abs, abs_abs]

/-- Lemma 4.1 decreases every finite family of modulus measurements simultaneously. -/
theorem orthogonal_reduction_measurementDistance (U : ι → L2 μ ≃ₗᵢ[ℂ] L2 μ)
    (f g : L2 μ) :
    ∃ u v : L2 μ, ⟪u, v⟫_ℂ = 0 ∧ ‖u‖ ^ 2 + ‖v‖ ^ 2 = phaseDistance f g ^ 2 ∧
      measurementDistance U u v ≤ measurementDistance U f g := by
  obtain ⟨u, v, _, _, huv, hn, hpoint⟩ := orthogonal_reduction_L2 (μ := μ) f g
  refine ⟨u, v, huv, hn, ?_⟩
  apply (pi_norm_le_iff_of_nonneg (measurementDistance_nonneg U f g)).mpr
  intro j
  exact (magnitudeDistance_mono_ae (hpoint (U j).toLinearEquiv.toLinearMap)).trans
    (norm_le_pi_norm (fun k => magnitude (U k f) - magnitude (U k g)) j)

/-- The homogeneity and orthogonal-reduction step at the end of Proposition 4.4. -/
theorem stableUnitaryFamily_of_normalized_orthogonal {c : ℝ}
    (U : ι → L2 μ ≃ₗᵢ[ℂ] L2 μ)
    (hU : ∀ u v : L2 μ, ⟪u, v⟫_ℂ = 0 → ‖u‖ ^ 2 + ‖v‖ ^ 2 = 1 →
      c ≤ measurementDistance U u v) : StableUnitaryFamily c U := by
  intro f g
  obtain ⟨u, v, huv, hn, hd⟩ := orthogonal_reduction_measurementDistance U f g
  by_cases hzero : phaseDistance f g = 0
  · simpa only [hzero, mul_zero] using measurementDistance_nonneg U f g
  have hpos : 0 < phaseDistance f g := lt_of_le_of_ne (phaseDistance_nonneg f g) (Ne.symm hzero)
  let a : ℝ := (phaseDistance f g)⁻¹
  have ha : 0 < a := inv_pos.mpr hpos
  have hnorm : ‖(a : ℂ) • u‖ ^ 2 + ‖(a : ℂ) • v‖ ^ 2 = 1 := by
    simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, mul_pow]
    rw [← mul_add, hn]
    dsimp [a]
    rw [← mul_pow, inv_mul_cancel₀ hzero, one_pow]
  have horth : ⟪(a : ℂ) • u, (a : ℂ) • v⟫_ℂ = 0 := by
    simp only [inner_smul_left, inner_smul_right, huv, mul_zero]
  have h := hU ((a : ℂ) • u) ((a : ℂ) • v) horth hnorm
  rw [measurementDistance_real_smul, abs_of_pos ha] at h
  have hmul := mul_le_mul_of_nonneg_left h hpos.le
  have he : phaseDistance f g * (a * measurementDistance U u v) = measurementDistance U u v := by
    dsimp [a]
    rw [← mul_assoc, mul_inv_cancel₀ hzero, one_mul]
  rw [he] at hmul
  have hfinal : c * phaseDistance f g ≤ measurementDistance U u v := by
    simpa only [mul_comm] using hmul
  exact hfinal.trans hd

end OperatorPhaseRetrieval

end
