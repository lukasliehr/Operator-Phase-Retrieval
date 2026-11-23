import OperatorPhaseRetrieval.HaarSphere
import OperatorPhaseRetrieval.ComplementUnitary
import OperatorPhaseRetrieval.TorusNet

/-!
# Haar small-ball probabilities

Lemma 4.3 is proved for canonical Haar probability on the unitary group.
Averaging over the subgroup fixing the first vector reduces the estimate to
`TorusNet` on the orthogonal-complement sphere. Right invariance and Tonelli
justify the averaging, so no conditional-distribution hypothesis is needed.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace OperatorPhaseRetrieval

theorem lintegral_le_of_right_averages {G H : Type*}
    [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableSpace H]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (ν : Measure H) [IsProbabilityMeasure ν]
    (S : H → G) (q : G → ℝ≥0∞) (hq : Measurable q)
    (hm : Measurable (fun p : G × H => q (p.1 * S p.2)))
    (B : ℝ≥0∞) (hB : ∀ g, (∫⁻ h, q (g * S h) ∂ν) ≤ B) :
    (∫⁻ g, q g ∂μ) ≤ B := by
  have hr (h : H) : (∫⁻ g, q (g * S h) ∂μ) = ∫⁻ g, q g ∂μ :=
    (measurePreserving_mul_right μ (S h)).lintegral_comp hq
  calc
    _ = ∫⁻ h, ∫⁻ g, q (g * S h) ∂μ ∂ν := by
      simp only [hr, lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ g, ∫⁻ h, q (g * S h) ∂ν ∂μ :=
      (lintegral_lintegral_swap hm.aemeasurable).symm
    _ ≤ ∫⁻ _g, B ∂μ := lintegral_mono hB
    _ = B := by simp

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem coordinateModulus_continuous : Continuous (coordinateModulus (ι := ι)) := by
  apply (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).comp
  exact continuous_pi fun i => (PiLp.continuous_apply 2 (fun _ : ι => ℂ) i).norm

omit [Fintype ι] in
@[simp] theorem coordinateModulus_zero : coordinateModulus (0 : EuclideanSpace ℂ ι) = 0 := by
  ext i
  simp [coordinateModulus]

def unitaryModulusDistance (x y : EuclideanSpace ℂ ι) (a b : ℝ)
    (u : HaarUnitary (EuclideanSpace ℂ ι)) : ℝ :=
  dist (b • coordinateModulus ((u : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) y))
    (a • coordinateModulus ((u : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) x))

theorem unitaryModulusDistance_continuous (x y : EuclideanSpace ℂ ι) (a b : ℝ) :
    Continuous (unitaryModulusDistance x y a b) := by
  apply Continuous.dist
  · exact (coordinateModulus_continuous.comp
      (continuous_subtype_val.clm_apply continuous_const)).const_smul b
  · exact (coordinateModulus_continuous.comp
      (continuous_subtype_val.clm_apply continuous_const)).const_smul a

/-- The Haar small-ball estimate for weighted orthonormal vectors. The proof
averages over unitaries of the orthogonal complement and uses right invariance
of Haar measure; no conditional-law hypothesis is assumed. -/
theorem haarUnitary_weighted_smallBall (hn : 3 ≤ Fintype.card ι)
    (x : EuclideanSpace ℂ ι) (hx : ‖x‖ = 1)
    (y : (ℂ ∙ x)ᗮ) (hy : ‖y‖ = 1)
    (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ^ 2 + b ^ 2 = 1)
    (ht : 0 < t) (ht1 : t ≤ 1 / 12) :
    (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure (HaarUnitary (EuclideanSpace ℂ ι)))
      {u | unitaryModulusDistance x y a b u ≤ t} ≤
      ENNReal.ofReal ((2 : ℝ) ^ (11 * Fintype.card ι) * t ^ (Fintype.card ι - 3)) := by
  let E := EuclideanSpace ℂ ι
  let K : Submodule ℂ E := ℂ ∙ x
  let F := Kᗮ
  let : InnerProductSpace ℝ F := InnerProductSpace.rclikeToReal ℂ F
  let : Nontrivial F := orthogonalComplement_nontrivial hn x hx
  let μ : Measure (HaarUnitary E) := haarUnitaryProbability E
  let ν : Measure (HaarUnitary F) := haarUnitaryProbability F
  let B := ENNReal.ofReal ((2 : ℝ) ^ (11 * Fintype.card ι) * t ^ (Fintype.card ι - 3))
  let S : HaarUnitary F → HaarUnitary E := complementUnitaryExtension K
  let A : Set (HaarUnitary E) := {u | unitaryModulusDistance x y a b u ≤ t}
  have hA : MeasurableSet A :=
    measurableSet_le (unitaryModulusDistance_continuous x y a b).measurable measurable_const
  let q : HaarUnitary E → ℝ≥0∞ := A.indicator (fun _ => 1)
  have hq : Measurable q := measurable_const.indicator hA
  have he (u : HaarUnitary E) (w : HaarUnitary F) :
      unitaryModulusDistance x y a b (u * S w) =
        dist (b • coordinateModulus ((u : E →L[ℂ] E) ((w : F →L[ℂ] F) y)))
          (a • coordinateModulus ((u : E →L[ℂ] E) x)) := by
    change dist (b • coordinateModulus ((u : E →L[ℂ] E) ((S w : E →L[ℂ] E) y)))
      (a • coordinateModulus ((u : E →L[ℂ] E) ((S w : E →L[ℂ] E) x))) = _
    have hfix := complementUnitaryExtension_fix K w ⟨x, Submodule.mem_span_singleton_self x⟩
    rw [show (S w : E →L[ℂ] E) x = x from hfix,
      show (S w : E →L[ℂ] E) y = ((w : F →L[ℂ] F) y : E) from
        complementUnitaryExtension_orthogonal K w y]
  have hc : Continuous (fun p : HaarUnitary E × HaarUnitary F =>
      unitaryModulusDistance x y a b (p.1 * S p.2)) := by
    simp only [he]
    apply Continuous.dist
    · exact (coordinateModulus_continuous.comp
        ((continuous_subtype_val.comp continuous_fst).clm_apply
          (continuous_subtype_val.comp
            ((continuous_subtype_val.comp continuous_snd).clm_apply continuous_const)))).const_smul b
    · exact (coordinateModulus_continuous.comp
        ((continuous_subtype_val.comp continuous_fst).clm_apply continuous_const)).const_smul a
  have hqm : Measurable (fun p : HaarUnitary E × HaarUnitary F => q (p.1 * S p.2)) := by
    exact measurable_const.indicator (measurableSet_le hc.measurable measurable_const)
  have hB (u : HaarUnitary E) : (∫⁻ w, q (u * S w) ∂ν) ≤ B := by
    let f : F →ₗᵢ[ℝ] E :=
      { toLinearMap := ((u : E →L[ℂ] E).toLinearMap.comp Kᗮ.subtype).restrictScalars ℝ
        norm_map' := fun z => Unitary.norm_map u (z : E) }
    let ys : sphere (0 : F) 1 := ⟨y, by simpa using hy⟩
    let C : Set (sphere (0 : F) 1) :=
      {z | dist (b • coordinateModulus (f (z : F)))
        (a • coordinateModulus ((u : E →L[ℂ] E) x)) ≤ t}
    have hC : MeasurableSet C := by
      apply measurableSet_le _ measurable_const
      exact ((coordinateModulus_continuous.comp
        (f.continuous.comp continuous_subtype_val)).const_smul b).dist continuous_const |>.measurable
    have hid : (∫⁻ w, q (u * S w) ∂ν) = (uniformSphere F : Measure _) C := by
      have hi := (haarUnitary_sphere_measurePreserving F ys).lintegral_comp
        (measurable_const.indicator hC : Measurable (C.indicator (fun _ => (1 : ℝ≥0∞))))
      have hci : (∫⁻ z, C.indicator (fun _ => (1 : ℝ≥0∞)) z ∂(uniformSphere F : Measure _)) =
          (uniformSphere F : Measure _) C := lintegral_indicator_one hC
      rw [hci] at hi
      convert hi using 1
      apply lintegral_congr
      intro w
      change A.indicator (fun _ => (1 : ℝ≥0∞)) (u * S w) =
        C.indicator (fun _ => (1 : ℝ≥0∞)) (unitarySphereAction F w ys)
      simp only [Set.indicator, mem_ofPred_eq, A, C, he]
      rfl
    rw [hid]
    have hd : Module.finrank ℝ F = 2 * Fintype.card ι - 2 := by
      rw [orthogonalComplement_real_finrank x hx]
      omega
    exact uniformSphere_scaled_modulus_smallBall hn hd f ((u : E →L[ℂ] E) x)
      (by rw [Unitary.norm_map, hx]) a b t ha hb hab ht ht1
  have h := lintegral_le_of_right_averages μ ν S q hq hqm B hB
  rwa [show (∫⁻ u, q u ∂μ) = μ A from lintegral_indicator_one hA] at h

omit [Fintype ι] in
theorem coordinateModulus_smul (c : ℂ) (z : EuclideanSpace ℂ ι) :
    coordinateModulus (c • z) = ‖c‖ • coordinateModulus z := by
  ext i
  change ‖c * z i‖ = ‖c‖ * ‖z i‖
  exact norm_mul c (z i)

/-- Lemma 4.3: the exact Haar small-ball estimate for any normalized orthogonal
pair, with no additional distributional or geometric hypotheses. -/
theorem haarUnitary_smallBall (hn : 3 ≤ Fintype.card ι)
    (u v : EuclideanSpace ℂ ι) (huv : inner ℂ u v = 0)
    (hnorm : ‖u‖ ^ 2 + ‖v‖ ^ 2 = 1) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1 / 12) :
    (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure (HaarUnitary (EuclideanSpace ℂ ι)))
      {w | dist (coordinateModulus ((w : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) u))
        (coordinateModulus ((w : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) v)) ≤ t} ≤
      ENNReal.ofReal ((2 : ℝ) ^ (11 * Fintype.card ι) * t ^ (Fintype.card ι - 3)) := by
  by_cases hu : u = 0
  · subst u
    have hv : ‖v‖ = 1 := by simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at hnorm; nlinarith [norm_nonneg v]
    have he : {w : HaarUnitary (EuclideanSpace ℂ ι) |
        dist (coordinateModulus ((w : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) 0)) (coordinateModulus ((w : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) v)) ≤ t} = ∅ := by
      ext w
      simp only [map_zero, coordinateModulus_zero,
        dist_zero_left, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      change ¬ ‖coordinateModulus ((w : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) v)‖ ≤ t
      rw [coordinateModulus_norm, Unitary.norm_map, hv]
      linarith
    rw [he, measure_empty]
    exact bot_le
  by_cases hv : v = 0
  · subst v
    have hu1 : ‖u‖ = 1 := by simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at hnorm; nlinarith [norm_nonneg u]
    have he : {w : HaarUnitary (EuclideanSpace ℂ ι) |
        dist (coordinateModulus ((w : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) u)) (coordinateModulus ((w : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) 0)) ≤ t} = ∅ := by
      ext w
      simp only [map_zero, coordinateModulus_zero,
        dist_zero_right, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      change ¬ ‖coordinateModulus ((w : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) u)‖ ≤ t
      rw [coordinateModulus_norm, Unitary.norm_map, hu1]
      linarith
    rw [he, measure_empty]
    exact bot_le
  let a := ‖u‖
  let b := ‖v‖
  have ha : 0 < a := norm_pos_iff.mpr hu
  have hb : 0 < b := norm_pos_iff.mpr hv
  let x : EuclideanSpace ℂ ι := ((a⁻¹ : ℝ) : ℂ) • u
  let z : EuclideanSpace ℂ ι := ((b⁻¹ : ℝ) : ℂ) • v
  have hx : ‖x‖ = 1 := by
    simp only [x, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos ha]
    exact inv_mul_cancel₀ ha.ne'
  have hz : ‖z‖ = 1 := by
    simp only [z, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hb]
    exact inv_mul_cancel₀ hb.ne'
  have hxz : inner ℂ x z = 0 := by
    simp only [x, z, inner_smul_left, inner_smul_right, huv, mul_zero]
  let y : (ℂ ∙ x)ᗮ := ⟨z, Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hxz⟩
  have hux : (a : ℂ) • x = u := by
    simp only [x, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ ha.ne', Complex.ofReal_one, one_smul]
  have hvz : (b : ℂ) • z = v := by
    simp only [z, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hb.ne', Complex.ofReal_one, one_smul]
  have he (w : HaarUnitary (EuclideanSpace ℂ ι)) :
      dist (coordinateModulus ((w : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) u)) (coordinateModulus ((w : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) v)) =
        unitaryModulusDistance x y a b w := by
    have hwu : (w : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) u = (a : ℂ) • ((w : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) x) := by rw [← hux, map_smul]
    have hwv : (w : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) v = (b : ℂ) • ((w : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) z) := by rw [← hvz, map_smul]
    rw [hwu, hwv, coordinateModulus_smul, coordinateModulus_smul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, abs_of_pos hb]
    exact dist_comm _ _
  simp only [he]
  exact haarUnitary_weighted_smallBall hn x hx y hz a b t ha.le hb.le hnorm ht ht1

end OperatorPhaseRetrieval

end
