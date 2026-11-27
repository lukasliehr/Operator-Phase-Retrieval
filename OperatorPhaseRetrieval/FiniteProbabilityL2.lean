import OperatorPhaseRetrieval.FiniteHaarTheorem
import OperatorPhaseRetrieval.Stability

/-! Finite normalized counting spaces and their actual measure-theoretic L² spaces. -/

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace OperatorPhaseRetrieval

variable (ι : Type*) [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]

/-- Counting measure divided by the cardinality of the finite sample space. -/
def finiteProbability : Measure ι := (Fintype.card ι : ℝ≥0∞)⁻¹ • Measure.count

instance finiteProbability_isProbabilityMeasure : IsProbabilityMeasure (finiteProbability ι) := by
  constructor
  simpa [finiteProbability, Measure.smul_apply] using
    (ENNReal.inv_mul_cancel (a := (Fintype.card ι : ℝ≥0∞))
      (by exact_mod_cast Fintype.card_ne_zero) (by simp))

omit [Nonempty ι] [MeasurableSingletonClass ι] in
theorem finiteProbability_ae_iff {p : ι → Prop} :
    (∀ᵐ i ∂finiteProbability ι, p i) ↔ ∀ i, p i := by
  rw [finiteProbability, Measure.ae_ennreal_smul_measure_iff (by simp), Measure.ae_count_iff]

omit [Nonempty ι] in
theorem finiteProbability_integral {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (f : ι → G) :
    ∫ i, f i ∂finiteProbability ι = (Fintype.card ι : ℝ)⁻¹ • ∑ i, f i := by
  simp [finiteProbability, integral_smul_measure, ENNReal.toReal_inv]

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The scaling by `sqrt(card ι)` identifies Euclidean norm with normalized L² norm. -/
def finiteL2Map : EuclideanSpace 𝕜 ι →ₗ[𝕜] Lp 𝕜 2 (finiteProbability ι) where
  toFun z := (MemLp.of_discrete (f := fun i => (Real.sqrt (Fintype.card ι) : ℝ) • z i)).toLp _
  map_add' z w := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (MemLp.of_discrete (f := fun i => (Real.sqrt (Fintype.card ι) : ℝ) • (z+w) i)),
      MemLp.coeFn_toLp (MemLp.of_discrete (f := fun i => (Real.sqrt (Fintype.card ι) : ℝ) • z i)),
      MemLp.coeFn_toLp (MemLp.of_discrete (f := fun i => (Real.sqrt (Fintype.card ι) : ℝ) • w i)),
      Lp.coeFn_add ((MemLp.of_discrete (f := fun i => (Real.sqrt (Fintype.card ι) : ℝ) • z i)).toLp _)
        ((MemLp.of_discrete (f := fun i => (Real.sqrt (Fintype.card ι) : ℝ) • w i)).toLp _)] with i hz hw hv ha
    simp only [Pi.add_apply, PiLp.add_apply] at *
    rw [hz, ha, hw, hv, smul_add]
  map_smul' c z := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (MemLp.of_discrete (f := fun i => (Real.sqrt (Fintype.card ι) : ℝ) • (c • z) i)),
      MemLp.coeFn_toLp (MemLp.of_discrete (f := fun i => (Real.sqrt (Fintype.card ι) : ℝ) • z i)),
      Lp.coeFn_smul c ((MemLp.of_discrete (f := fun i => (Real.sqrt (Fintype.card ι) : ℝ) • z i)).toLp _)] with i hc hz hs
    simp only [RingHom.id_apply, Pi.smul_apply, PiLp.smul_apply] at *
    rw [hc, hs, hz, smul_comm]

theorem finiteL2Map_apply (z : EuclideanSpace 𝕜 ι) (i : ι) :
    finiteL2Map ι 𝕜 z i = (Real.sqrt (Fintype.card ι) : ℝ) • z i :=
  (finiteProbability_ae_iff ι).mp MemLp.of_discrete.coeFn_toLp i

omit [Nonempty ι] in
theorem finiteL2_norm_sq (f : Lp 𝕜 2 (finiteProbability ι)) :
    ‖f‖ ^ 2 = (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖f i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq f, MeasureTheory.L2.inner_def]
  simp_rw [real_inner_self_eq_norm_sq]
  exact finiteProbability_integral ι _

theorem finiteL2Map_norm (z : EuclideanSpace 𝕜 ι) : ‖finiteL2Map ι 𝕜 z‖ = ‖z‖ := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : ‖finiteL2Map ι 𝕜 z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [finiteL2_norm_sq]
    simp_rw [finiteL2Map_apply, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ hn, one_mul,
      PiLp.norm_sq_eq_of_L2]
  nlinarith [norm_nonneg z, norm_nonneg (finiteL2Map ι 𝕜 z)]

theorem finiteL2Map_surjective : Function.Surjective (finiteL2Map ι 𝕜) := by
  intro f
  have hn : Real.sqrt (Fintype.card ι) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)).ne'
  refine ⟨WithLp.toLp 2 (fun i => (Real.sqrt (Fintype.card ι))⁻¹ • f i), ?_⟩
  apply Lp.ext
  apply Filter.Eventually.of_forall
  intro i
  rw [finiteL2Map_apply]
  change Real.sqrt (Fintype.card ι) • ((Real.sqrt (Fintype.card ι))⁻¹ • f i) = f i
  rw [smul_smul, mul_inv_cancel₀ hn, one_smul]

def finiteL2Equiv : EuclideanSpace 𝕜 ι ≃ₗᵢ[𝕜] Lp 𝕜 2 (finiteProbability ι) :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := finiteL2Map ι 𝕜, norm_map' := finiteL2Map_norm ι 𝕜 }
    (finiteL2Map_surjective ι 𝕜)

theorem finiteL2Equiv_apply (z : EuclideanSpace 𝕜 ι) (i : ι) :
    finiteL2Equiv ι 𝕜 z i = (Real.sqrt (Fintype.card ι) : ℝ) • z i :=
  finiteL2Map_apply ι 𝕜 z i

/-- The finite identification commutes with taking coordinate magnitudes. -/
theorem finiteL2Equiv_magnitude (z : EuclideanSpace ℂ ι) :
    finiteL2Equiv ι ℝ (coordinateModulus z) = magnitude (finiteL2Equiv ι ℂ z) := by
  apply Lp.ext
  apply Filter.Eventually.of_forall
  intro i
  rw [finiteL2Equiv_apply, (finiteProbability_ae_iff ι).mp (magnitude_coeFn _) i]
  change _ = ‖finiteL2Equiv ι ℂ z i‖
  rw [finiteL2Equiv_apply]
  simp only [coordinateModulus, WithLp.ofLp_toLp, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), smul_eq_mul]

theorem finiteL2Equiv_magnitudeDistance (z w : EuclideanSpace ℂ ι) :
    ‖magnitude (finiteL2Equiv ι ℂ z) - magnitude (finiteL2Equiv ι ℂ w)‖ =
      dist (coordinateModulus z) (coordinateModulus w) := by
  rw [← finiteL2Equiv_magnitude, ← finiteL2Equiv_magnitude, ← map_sub,
    (finiteL2Equiv ι ℝ).norm_map, dist_eq_norm]

theorem finiteL2Equiv_phaseDistance (z w : EuclideanSpace ℂ ι) :
    phaseDistance (finiteL2Equiv ι ℂ z) (finiteL2Equiv ι ℂ w) = phaseDistance z w :=
  phaseDistance_map (finiteL2Equiv ι ℂ).toLinearIsometry z w

/-- A genuine surjective unitary on the measure-theoretic normalized finite L² space. -/
def finiteL2Unitary (U : HaarUnitary (EuclideanSpace ℂ ι)) :
    L2 (finiteProbability ι) ≃ₗᵢ[ℂ] L2 (finiteProbability ι) :=
  ((finiteL2Equiv ι ℂ).symm.trans (Unitary.linearIsometryEquiv U)).trans (finiteL2Equiv ι ℂ)

theorem finiteL2Unitary_apply (U : HaarUnitary (EuclideanSpace ℂ ι))
    (z : EuclideanSpace ℂ ι) :
    finiteL2Unitary ι U (finiteL2Equiv ι ℂ z) =
      finiteL2Equiv ι ℂ ((U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) z) := by
  simp only [finiteL2Unitary, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply]
  rfl

/-- The normalization preserves the full uniform stability statement. -/
theorem finiteL2Unitary_stable_iff (c : ℝ) (U : Fin 5 → HaarUnitary (EuclideanSpace ℂ ι)) :
    StableUnitaryFamily c (fun j => finiteL2Unitary ι (U j)) ↔ coordinateStableFamily c U := by
  constructor
  · intro h f g
    have hb := h (finiteL2Equiv ι ℂ f) (finiteL2Equiv ι ℂ g)
    rw [finiteL2Equiv_phaseDistance] at hb
    obtain ⟨j, hj⟩ := (IsGreatest.pi_norm (fun j : Fin 5 =>
      magnitude (finiteL2Unitary ι (U j) (finiteL2Equiv ι ℂ f)) -
        magnitude (finiteL2Unitary ι (U j) (finiteL2Equiv ι ℂ g)))).1
    refine ⟨j, ?_⟩
    change c * phaseDistance f g ≤ dist (coordinateModulus ((U j : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) f))
      (coordinateModulus ((U j : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) g))
    rw [← finiteL2Equiv_magnitudeDistance]
    have hb' := hb.trans_eq hj.symm
    simpa only [finiteL2Unitary_apply] using hb'
  · intro h f g
    let z := (finiteL2Equiv ι ℂ).symm f
    let w := (finiteL2Equiv ι ℂ).symm g
    obtain ⟨j, hj⟩ := h z w
    have hf : finiteL2Equiv ι ℂ z = f := (finiteL2Equiv ι ℂ).apply_symm_apply f
    have hg : finiteL2Equiv ι ℂ w = g := (finiteL2Equiv ι ℂ).apply_symm_apply g
    rw [← hf, ← hg, finiteL2Equiv_phaseDistance]
    calc
      c * phaseDistance z w ≤ pairModulusDistance (U j) (WithLp.toLp 2 (z, w)) := hj
      _ = ‖magnitude (finiteL2Unitary ι (U j) (finiteL2Equiv ι ℂ z)) -
          magnitude (finiteL2Unitary ι (U j) (finiteL2Equiv ι ℂ w))‖ := by
        rw [finiteL2Unitary_apply, finiteL2Unitary_apply, finiteL2Equiv_magnitudeDistance]
        rfl
      _ ≤ _ := norm_le_pi_norm
        (fun k : Fin 5 => magnitude (finiteL2Unitary ι (U k) (finiteL2Equiv ι ℂ z)) -
          magnitude (finiteL2Unitary ι (U k) (finiteL2Equiv ι ℂ w))) j

/-- The finite-dimensional stability estimate on the normalized finite probability spaces. -/
theorem finiteL2_haar_stability_failure_le (hn : 50 ≤ Fintype.card ι) :
    (haarFiveProbability ι : Measure (Fin 5 → HaarUnitary (EuclideanSpace ℂ ι)))
      {U | ¬ StableUnitaryFamily stabilityConstant (fun j => finiteL2Unitary ι (U j))} ≤
      ENNReal.ofReal ((2 : ℝ) ^ (1485 - 32 * (Fintype.card ι : ℤ))) := by
  have hc : stabilityConstant = (2 : ℝ) ^ (-100 : ℤ) := by norm_num [stabilityConstant, zpow_neg]
  simp_rw [finiteL2Unitary_stable_iff, hc]
  exact haarFive_stability_failure_le hn

/-- Stable five-unitary families on actual finite probability-space L², with the
first measurement normalized to the identity and the exact two-sided bound. -/
theorem fiveUnitaryStability_finiteProbability (hn : 50 ≤ Fintype.card ι) :
    FiveUnitaryStability (finiteProbability ι) := by
  obtain ⟨U, hU⟩ := exists_five_stable_finite hn
  apply fiveUnitaryStability_of_family (fun j => finiteL2Unitary ι (U j))
  apply (finiteL2Unitary_stable_iff ι _ _).mpr
  convert hU using 1
  norm_num [stabilityConstant, zpow_neg]

end OperatorPhaseRetrieval

end
