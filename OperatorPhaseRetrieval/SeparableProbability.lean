module

public import OperatorPhaseRetrieval.ProbabilitySpatial
public import OperatorPhaseRetrieval.WeightedL2

@[expose] public section

/-! A standard Borel model for an arbitrary separable atomless probability space. -/

noncomputable section

open MeasureTheory Set Filter TopologicalSpace
open scoped Topology

namespace OperatorPhaseRetrieval

/-- Atomlessness in the set-splitting sense, including sets of infinite measure. -/
def AtomlessMeasure {X : Type*} [MeasurableSpace X] (μ : Measure X) : Prop :=
  ∀ s, MeasurableSet s → 0 < μ s →
    ∃ t, t ⊆ s ∧ MeasurableSet t ∧ 0 < μ t ∧ 0 < μ (s \ t)

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y}

theorem AtomlessMeasure.of_equivalent (hμ : AtomlessMeasure μ)
    {ρ : Measure X} (hρμ : ρ ≪ μ) (hμρ : μ ≪ ρ) : AtomlessMeasure ρ := by
  intro s hs hpos
  have hm : 0 < μ s := bot_lt_iff_ne_bot.mpr (fun hz => hpos.ne' (hρμ hz))
  obtain ⟨t, hts, ht, htp, hsp⟩ := hμ s hs hm
  exact ⟨t, hts, ht, bot_lt_iff_ne_bot.mpr (fun hz => htp.ne' (hμρ hz)),
    bot_lt_iff_ne_bot.mpr (fun hz => hsp.ne' (hμρ hz))⟩

theorem isometry_surjective_of_dense {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (T : H →ₗᵢ[ℂ] G) (u : ℕ → G) (hu : DenseRange u)
    (h : ∀ n, u n ∈ Set.range T) : Function.Surjective T := by
  intro g
  exact hu.induction_on g T.isometry.isClosedEmbedding.isClosed_range h

theorem pullback_modEq_iff (F : X → Y) (hF : MeasurePreserving F μ ν)
    (f g : L2 ν) :
    ModEq (Lp.compMeasurePreserving F hF f) (Lp.compMeasurePreserving F hF g) ↔
      ModEq f g := by
  constructor
  · intro h
    have he : ∀ᵐ x ∂μ, ‖f (F x)‖ = ‖g (F x)‖ := by
      filter_upwards [h, Lp.coeFn_compMeasurePreserving f hF,
        Lp.coeFn_compMeasurePreserving g hF] with x hx hf hg
      simpa only [hf, hg, Function.comp_apply] using hx
    have hr := (ae_map_iff hF.aemeasurable
      (measurableSet_eq_fun (Lp.stronglyMeasurable f).measurable.norm
        (Lp.stronglyMeasurable g).measurable.norm)).mpr he
    simpa only [hF.map_eq, ModEq] using hr
  · exact pullback_modEq_forward F hF

/-- A surjective pullback to an atomless probability space has null singleton fibers. -/
theorem nullSingleton_of_surjective_pullback [IsProbabilityMeasure μ]
    [MeasurableSingletonClass Y] (hμ : AtomlessMeasure μ)
    (F : X → Y) (hF : MeasurePreserving F μ ν)
    (hsurj : Function.Surjective
      (Lp.compMeasurePreservingₗᵢ ℂ F hF : L2 ν →ₗᵢ[ℂ] L2 μ)) :
    NullSingletonClass ν := by
  constructor
  intro y
  by_contra hy
  let s := F ⁻¹' {y}
  have hs : MeasurableSet s := hF.measurable (measurableSet_singleton y)
  have hpos : 0 < μ s := by
    rw [show μ s = ν {y} from hF.measure_preimage (measurableSet_singleton y).nullMeasurableSet]
    exact bot_lt_iff_ne_bot.mpr hy
  obtain ⟨t, hts, ht, htp, hsp⟩ := hμ s hs hpos
  obtain ⟨a, ha⟩ := hsurj (indicatorConstLp 2 ht (measure_ne_top μ t) (1 : ℂ))
  have he : ∀ᵐ x ∂μ, a (F x) = t.indicator (fun _ => (1 : ℂ)) x := by
    have hp := Lp.coeFn_compMeasurePreserving a hF
    change (Lp.compMeasurePreserving F hF a : X → ℂ) =ᵐ[μ] _ at hp
    have ha' : Lp.compMeasurePreserving F hF a =
        indicatorConstLp 2 ht (measure_ne_top μ t) (1 : ℂ) := ha
    rw [ha'] at hp
    exact hp.symm.trans indicatorConstLp_coeFn
  have hmem : ∀ᵐ x ∂μ, x ∈ t → a y = 1 := by
    filter_upwards [he] with x hx hxt
    have hxy : F x = y := hts hxt
    simpa [hxy, hxt] using hx
  have hnot : ∀ᵐ x ∂μ, x ∈ s \ t → a y = 0 := by
    filter_upwards [he] with x hx hxt
    have hxy : F x = y := hxt.1
    simpa [hxy, hxt.2] using hx
  obtain ⟨_, _, hone⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae htp.ne'
    ((ae_restrict_iff' ht).mpr hmem)
  obtain ⟨_, _, hzero⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hsp.ne'
    ((ae_restrict_iff' (hs.diff ht)).mpr hnot)
  exact one_ne_zero (hone.symm.trans hzero)

/-- Dense coordinates give a standard probability model without a pointwise inverse. -/
theorem separable_probability_spatial_unitary [IsProbabilityMeasure μ]
    [SeparableSpace (L2 μ)] (hμ : AtomlessMeasure μ) :
    ∃ W : L2 uniformUnit ≃ₗᵢ[ℂ] L2 μ,
      ∀ f g, ModEq (W f) (W g) ↔ ModEq f g := by
  obtain ⟨u, hu⟩ := exists_dense_seq (L2 μ)
  let F : X → (ℕ → ℂ) := fun x n => u n x
  have hm : Measurable F := measurable_pi_iff.mpr (fun n =>
    (Lp.stronglyMeasurable (u n)).measurable)
  let ρ := Measure.map F μ
  have hF : MeasurePreserving F μ ρ := ⟨hm, rfl⟩
  let : IsProbabilityMeasure ρ := inferInstanceAs (IsProbabilityMeasure (Measure.map F μ))
  let T : L2 ρ →ₗᵢ[ℂ] L2 μ := Lp.compMeasurePreservingₗᵢ ℂ F hF
  have hs : Function.Surjective T := by
    apply isometry_surjective_of_dense T u hu
    intro n
    have hc : MemLp (fun z : ℕ → ℂ => z n) 2 ρ :=
      (memLp_map_measure_iff (measurable_pi_apply n).aestronglyMeasurable
        hm.aemeasurable).mpr (Lp.memLp (u n))
    refine ⟨hc.toLp _, ?_⟩
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (hc.toLp _) hF,
      hF.quasiMeasurePreserving.ae hc.coeFn_toLp] with x hx hy
    exact hx.trans hy
  let : NullSingletonClass ρ := nullSingleton_of_surjective_pullback hμ F hF hs
  obtain ⟨A, hA⟩ := probability_spatial_unitary ρ
  let B := LinearIsometryEquiv.ofSurjective T hs
  exact ⟨A.trans B, fun f g => (pullback_modEq_iff F hF (A f) (A g)).trans (hA f g)⟩

end OperatorPhaseRetrieval

end
