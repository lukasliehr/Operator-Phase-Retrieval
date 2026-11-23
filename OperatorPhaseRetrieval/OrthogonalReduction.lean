import OperatorPhaseRetrieval.PhaseDistance

/-! # Orthogonal-pair reduction (Lemma 4.1)

The pointwise contraction underlying the reduction works for arbitrary complex
numbers and therefore for every linear measurement at every point.
-/

noncomputable section

open scoped InnerProductSpace

namespace OperatorPhaseRetrieval

/-- The scalar mixing used in Lemma 4.1. -/
def mixScalar (t : ℝ) (z w : ℂ) : ℂ := (1 - (t : ℂ)) * z - (t : ℂ) * w

theorem mixScalar_norm_sq_sub (t : ℝ) (z w : ℂ) :
    ‖mixScalar t z w‖ ^ 2 - ‖mixScalar t w z‖ ^ 2 =
      (1 - 2 * t) * (‖z‖ ^ 2 - ‖w‖ ^ 2) := by
  simp only [← Complex.normSq_eq_norm_sq, mixScalar, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem mixScalar_norm_sum (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) (z w : ℂ) :
    (1 - 2 * t) * (‖z‖ + ‖w‖) ≤ ‖mixScalar t z w‖ + ‖mixScalar t w z‖ := by
  have h₁ := norm_sub_norm_le ((1 - (t : ℂ)) * z) ((t : ℂ) * w)
  have h₂ := norm_sub_norm_le ((1 - (t : ℂ)) * w) ((t : ℂ) * z)
  have ha : ‖1 - (t : ℂ)‖ = 1 - t := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  simp only [norm_mul, ha, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht] at h₁ h₂
  change (1 - 2 * t) * (‖z‖ + ‖w‖) ≤
    ‖(1 - (t : ℂ)) * z - (t : ℂ) * w‖ + ‖(1 - (t : ℂ)) * w - (t : ℂ) * z‖
  linarith

/-- Pointwise modulus-distance contraction, with all zero cases included. -/
theorem mixScalar_modulus_contraction (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1 / 2)
    (z w : ℂ) :
    |‖mixScalar t z w‖ - ‖mixScalar t w z‖| ≤ |‖z‖ - ‖w‖| := by
  let A := ‖mixScalar t z w‖
  let B := ‖mixScalar t w z‖
  have hA : 0 ≤ A := norm_nonneg _
  have hB : 0 ≤ B := norm_nonneg _
  have ha : 0 ≤ 1 - 2 * t := by linarith
  have hs := mixScalar_norm_sum t ht ht' z w
  have he := congrArg abs (mixScalar_norm_sq_sub t z w)
  have factor (a b : ℝ) : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  rw [factor, factor, abs_mul, abs_mul, abs_mul, abs_of_nonneg ha,
    abs_of_nonneg (add_nonneg hA hB),
    abs_of_nonneg (add_nonneg (norm_nonneg z) (norm_nonneg w))] at he
  change |A - B| * (A + B) = _ at he
  change (1 - 2 * t) * (‖z‖ + ‖w‖) ≤ A + B at hs
  change |A - B| ≤ |‖z‖ - ‖w‖|
  by_cases hzero : A + B = 0
  · have hA0 : A = 0 := by linarith
    have hB0 : B = 0 := by linarith
    simp [hA0, hB0]
  · have hpos : 0 < A + B := lt_of_le_of_ne (add_nonneg hA hB) (Ne.symm hzero)
    apply (mul_le_mul_iff_left₀ hpos).mp
    nlinarith [mul_le_mul_of_nonneg_left hs (abs_nonneg (‖z‖ - ‖w‖))]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def mixVector (t : ℝ) (f g : H) : H := (1 - (t : ℂ)) • f - (t : ℂ) • g

theorem mixVector_sub (t : ℝ) (f g : H) : mixVector t f g - mixVector t g f = f - g := by
  unfold mixVector
  module

theorem mixVector_inner (t : ℝ) (f g : H) {q : ℝ} (hfg : ⟪f, g⟫_ℂ = (q : ℂ)) :
    ⟪mixVector t f g, mixVector t g f⟫_ℂ =
      ((q - t * (1 - t) * ‖f + g‖ ^ 2 : ℝ) : ℂ) := by
  have hgf : ⟪g, f⟫_ℂ = (q : ℂ) := by
    rw [← inner_conj_symm g f, hfg]
    simp
  have hnorm := norm_add_sq (𝕜 := ℂ) f g
  simp only [hfg, RCLike.re_eq_complex_re, Complex.ofReal_re] at hnorm
  simp only [mixVector, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, hfg, hgf, inner_self_eq_norm_sq_to_K,
    map_sub, map_one, Complex.conj_ofReal]
  rw [hnorm]
  simp only [RCLike.ofReal_eq_complex_ofReal]
  push_cast
  ring

theorem exists_orthogonal_mix (f g : H) {q : ℝ} (hq : 0 ≤ q)
    (hfg : ⟪f, g⟫_ℂ = (q : ℂ)) :
    ∃ t : ℝ, t ∈ Set.Icc 0 (1 / 2) ∧ ⟪mixVector t f g, mixVector t g f⟫_ℂ = 0 := by
  let F : ℝ → ℝ := fun t => q - t * (1 - t) * ‖f + g‖ ^ 2
  have hc : Continuous F :=
    continuous_const.sub ((continuous_id.mul (continuous_const.sub continuous_id)).mul continuous_const)
  have hnorm := norm_add_sq (𝕜 := ℂ) f g
  have hsub := norm_sub_sq (𝕜 := ℂ) f g
  simp only [hfg, RCLike.re_eq_complex_re, Complex.ofReal_re] at hnorm hsub
  have h0 : 0 ∈ Set.Icc (F (1 / 2)) (F 0) := by
    constructor
    · dsimp [F]
      nlinarith [sq_nonneg ‖f - g‖]
    · simpa [F] using hq
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1 / 2)
    hc.continuousOn h0
  refine ⟨t, ht, ?_⟩
  rw [mixVector_inner t f g hfg]
  change (F t : ℂ) = 0
  rw [he, Complex.ofReal_zero]

/-- Lemma 4.1, in a form valid even when the phase distance is zero.
The scalar-functional conclusion yields the pointwise assertion for every
linear map into a space of functions. -/
theorem orthogonal_reduction (f g : H) :
    ∃ u v : H, u ∈ Submodule.span ℂ ({f, g} : Set H) ∧
      v ∈ Submodule.span ℂ ({f, g} : Set H) ∧
      ⟪u, v⟫_ℂ = 0 ∧ ‖u‖ ^ 2 + ‖v‖ ^ 2 = phaseDistance f g ^ 2 ∧
      ∀ T : H →ₗ[ℂ] ℂ, |‖T u‖ - ‖T v‖| ≤ |‖T f‖ - ‖T g‖| := by
  obtain ⟨ω, hω, hd, hi⟩ := phaseDistance_attained f g
  obtain ⟨t, ht, ho⟩ := exists_orthogonal_mix f (ω • g) (norm_nonneg _) hi
  let u := mixVector t f (ω • g)
  let v := mixVector t (ω • g) f
  have hf : f ∈ Submodule.span ℂ ({f, g} : Set H) := Submodule.subset_span (by simp)
  have hg : g ∈ Submodule.span ℂ ({f, g} : Set H) := Submodule.subset_span (by simp)
  have hwg := (Submodule.span ℂ ({f, g} : Set H)).smul_mem ω hg
  refine ⟨u, v, ?_, ?_, ho, ?_, ?_⟩
  · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hf) (Submodule.smul_mem _ _ hwg)
  · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hwg) (Submodule.smul_mem _ _ hf)
  · have hn := norm_sub_sq (𝕜 := ℂ) u v
    rw [ho, map_zero, mul_zero, sub_zero] at hn
    rw [← hn, mixVector_sub, hd]
  · intro T
    have h := mixScalar_modulus_contraction t ht.1 ht.2 (T f) (ω * T g)
    simpa only [u, v, mixVector, map_sub, map_smul, smul_eq_mul, mixScalar,
      norm_mul, show ‖ω‖ = 1 from hω, one_mul] using h

open MeasureTheory

theorem mixVector_map_coeFn {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (T : H →ₗ[ℂ] L2 μ) (t : ℝ) (f g : H) :
    (T (mixVector t f g) : X → ℂ) =ᵐ[μ] (fun x => mixScalar t (T f x) (T g x)) := by
  simp only [mixVector, map_sub, map_smul]
  filter_upwards [Lp.coeFn_sub ((1 - (t : ℂ)) • T f) ((t : ℂ) • T g),
    Lp.coeFn_smul (1 - (t : ℂ)) (T f), Lp.coeFn_smul (t : ℂ) (T g)] with x hs hf hg
  simp only [Pi.sub_apply, Pi.smul_apply] at hs hf hg
  rw [hs, hf, hg]
  rfl

/-- Lemma 4.1 for arbitrary linear L² measurements, including the a.e. bookkeeping. -/
theorem orthogonal_reduction_L2 {X : Type*} [MeasurableSpace X] {μ : Measure X} (f g : H) :
    ∃ u v : H, u ∈ Submodule.span ℂ ({f, g} : Set H) ∧
      v ∈ Submodule.span ℂ ({f, g} : Set H) ∧
      ⟪u, v⟫_ℂ = 0 ∧ ‖u‖ ^ 2 + ‖v‖ ^ 2 = phaseDistance f g ^ 2 ∧
      ∀ T : H →ₗ[ℂ] L2 μ, ∀ᵐ x ∂μ, |‖T u x‖ - ‖T v x‖| ≤ |‖T f x‖ - ‖T g x‖| := by
  obtain ⟨ω, hω, hd, hi⟩ := phaseDistance_attained f g
  obtain ⟨t, ht, ho⟩ := exists_orthogonal_mix f (ω • g) (norm_nonneg _) hi
  let u := mixVector t f (ω • g)
  let v := mixVector t (ω • g) f
  have hf : f ∈ Submodule.span ℂ ({f, g} : Set H) := Submodule.subset_span (by simp)
  have hg : g ∈ Submodule.span ℂ ({f, g} : Set H) := Submodule.subset_span (by simp)
  have hwg := (Submodule.span ℂ ({f, g} : Set H)).smul_mem ω hg
  refine ⟨u, v, ?_, ?_, ho, ?_, ?_⟩
  · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hf) (Submodule.smul_mem _ _ hwg)
  · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hwg) (Submodule.smul_mem _ _ hf)
  · have hn := norm_sub_sq (𝕜 := ℂ) u v
    rw [ho, map_zero, mul_zero, sub_zero] at hn
    rw [← hn, mixVector_sub, hd]
  · intro T
    have hw : (T (ω • g) : X → ℂ) =ᵐ[μ] (fun x => ω * T g x) := by
      rw [T.map_smul]
      exact Lp.coeFn_smul ω (T g)
    filter_upwards [mixVector_map_coeFn T t f (ω • g),
      mixVector_map_coeFn T t (ω • g) f, hw] with x h₁ h₂ h₃
    change |‖T (mixVector t f (ω • g)) x‖ - ‖T (mixVector t (ω • g) f) x‖| ≤ _
    rw [h₁, h₂, h₃]
    simpa only [norm_mul, show ‖ω‖ = 1 from hω, one_mul] using
      mixScalar_modulus_contraction t ht.1 ht.2 (T f x) (ω * T g x)

end OperatorPhaseRetrieval

end
