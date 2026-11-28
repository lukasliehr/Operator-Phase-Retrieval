module

public import OperatorPhaseRetrieval.SeparableProbability

@[expose] public section

/-! A σ-finite part supporting every function in a separable L² space. -/

noncomputable section

open MeasureTheory Set Filter TopologicalSpace
open scoped Topology

namespace OperatorPhaseRetrieval

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {s : Set X}

/-- Extension by zero as an L² function. -/
def zeroExtendL2Fun (hs : MeasurableSet s) (f : L2 (μ.restrict s)) : L2 μ :=
  ((memLp_indicator_iff_restrict hs.nullMeasurableSet).mpr (Lp.memLp f)).toLp _

theorem zeroExtendL2Fun_coeFn (hs : MeasurableSet s) (f : L2 (μ.restrict s)) :
    (zeroExtendL2Fun hs f : X → ℂ) =ᵐ[μ] s.indicator (fun x => f x) :=
  MemLp.coeFn_toLp _

/-- Extension by zero from a restricted measure, with no σ-finiteness assumption. -/
def zeroExtendL2 (hs : MeasurableSet s) : L2 (μ.restrict s) →ₗᵢ[ℂ] L2 μ where
  toFun := zeroExtendL2Fun hs
  map_add' f g := by
    apply Lp.ext
    have he := (ae_eq_restrict_iff_indicator_ae_eq hs).mp (Lp.coeFn_add f g)
    filter_upwards [zeroExtendL2Fun_coeFn hs (f+g), zeroExtendL2Fun_coeFn hs f,
      zeroExtendL2Fun_coeFn hs g, Lp.coeFn_add (zeroExtendL2Fun hs f) (zeroExtendL2Fun hs g), he]
      with x hx hf hg ha heq
    simp only [Pi.add_apply] at ha
    rw [hx, ha, hf, hg, heq]
    by_cases hxs : x ∈ s <;> simp [hxs]
  map_smul' c f := by
    apply Lp.ext
    have he := (ae_eq_restrict_iff_indicator_ae_eq hs).mp (Lp.coeFn_smul c f)
    filter_upwards [zeroExtendL2Fun_coeFn hs (c • f), zeroExtendL2Fun_coeFn hs f,
      Lp.coeFn_smul c (zeroExtendL2Fun hs f), he] with x hx hf ha heq
    change zeroExtendL2Fun hs (c • f) x = (c • zeroExtendL2Fun hs f) x
    simp only [Pi.smul_apply] at ha
    rw [hx, ha, hf, heq]
    by_cases hxs : x ∈ s <;> simp [hxs]
  norm_map' f := by
    change ‖zeroExtendL2Fun hs f‖ = ‖f‖
    rw [zeroExtendL2Fun, Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet, Lp.norm_def]

theorem zeroExtendL2_coeFn (hs : MeasurableSet s) (f : L2 (μ.restrict s)) :
    (zeroExtendL2 hs f : X → ℂ) =ᵐ[μ] s.indicator (fun x => f x) :=
  zeroExtendL2Fun_coeFn hs f

theorem zeroExtendL2_modEq (hs : MeasurableSet s) (f g : L2 (μ.restrict s)) :
    ModEq (zeroExtendL2 hs f) (zeroExtendL2 hs g) ↔ ModEq f g := by
  rw [ModEq, ModEq, ae_restrict_iff' hs]
  constructor
  · intro h
    filter_upwards [h, zeroExtendL2_coeFn hs f, zeroExtendL2_coeFn hs g]
      with x hx hf hg hxs
    simpa only [hf, hg, Set.indicator_of_mem hxs] using hx
  · intro h
    filter_upwards [h, zeroExtendL2_coeFn hs f, zeroExtendL2_coeFn hs g]
      with x hx hf hg
    rw [hf, hg]
    by_cases hxs : x ∈ s
    · simpa only [Set.indicator_of_mem hxs] using hx hxs
    · simp only [Set.indicator_of_notMem hxs]

theorem zeroExtendL2_restrict (hs : MeasurableSet s) (f : L2 μ)
    (hf : (f : X → ℂ) =ᵐ[μ.restrict sᶜ] 0) :
    zeroExtendL2 hs (((Lp.memLp f).restrict s).toLp f) = f := by
  apply Lp.ext
  exact (zeroExtendL2_coeFn hs _).trans
    (((ae_eq_restrict_iff_indicator_ae_eq hs).mp
      ((Lp.memLp f).restrict s).coeFn_toLp).trans
      (indicator_ae_eq_of_restrict_compl_ae_eq_zero hs hf))

theorem sigmaFinite_restrict_countable_union (t : ℕ → Set X)
    (ht : ∀ n, MeasurableSet (t n)) (hfin : ∀ n, SigmaFinite (μ.restrict (t n))) :
    SigmaFinite (μ.restrict (⋃ n, t n)) := by
  let (n : ℕ) : SigmaFinite (μ.restrict (t n)) := hfin n
  let s := ⋃ n, t n
  let A : ℕ × ℕ → Set X := fun p => spanningSets (μ.restrict (t p.1)) p.2 ∩ t p.1
  have hA (p : ℕ × ℕ) : MeasurableSet (A p) :=
    (measurableSet_spanningSets _ _).inter (ht _)
  have hAf (p : ℕ × ℕ) : μ (A p) < ⊤ := by
    rw [show μ (A p) = (μ.restrict (t p.1)) (spanningSets (μ.restrict (t p.1)) p.2) by
      rw [Measure.restrict_apply (measurableSet_spanningSets _ _)]]
    exact measure_spanningSets_lt_top _ _
  apply Measure.sigmaFinite_of_countable (S := insert sᶜ (Set.range A))
    ((Set.countable_range A).insert sᶜ)
  · intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ⟨p, rfl⟩
    · change (μ.restrict s) sᶜ < ⊤
      rw [Measure.restrict_apply (MeasurableSet.iUnion ht).compl]
      change μ (sᶜ ∩ s) < ⊤
      simp
    · exact lt_of_le_of_lt (Measure.restrict_le_self (A p)) (hAf p)
  · apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ s
    · obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      obtain ⟨k, hk⟩ := mem_iUnion.mp (show x ∈ ⋃ k, spanningSets (μ.restrict (t n)) k by
        rw [iUnion_spanningSets]; trivial)
      exact Set.mem_sUnion.mpr ⟨A (n,k), Set.mem_insert_of_mem _ (Set.mem_range_self _), hk, hn⟩
    · exact Set.mem_sUnion.mpr ⟨sᶜ, Set.mem_insert _ _, hx⟩

/-- The complement need not be null: it is invisible to all L² functions. -/
theorem exists_sigmaFinite_L2_model [SeparableSpace (L2 μ)] :
    ∃ s, MeasurableSet s ∧ SigmaFinite (μ.restrict s) ∧
      ∃ W : L2 (μ.restrict s) ≃ₗᵢ[ℂ] L2 μ,
        ∀ f g, ModEq (W f) (W g) ↔ ModEq f g := by
  obtain ⟨u, hu⟩ := exists_dense_seq (L2 μ)
  have hf (n : ℕ) := ((Lp.memLp (u n)).aefinStronglyMeasurable
    (by norm_num) (by norm_num)).exists_set_sigmaFinite
  choose t ht hz hfin using hf
  let s := ⋃ n, t n
  have hs : MeasurableSet s := MeasurableSet.iUnion ht
  refine ⟨s, hs, sigmaFinite_restrict_countable_union t ht hfin, ?_⟩
  have hsurj : Function.Surjective (zeroExtendL2 (μ := μ) hs) := by
    apply isometry_surjective_of_dense _ u hu
    intro n
    refine ⟨((Lp.memLp (u n)).restrict s).toLp _, zeroExtendL2_restrict hs (u n) ?_⟩
    apply (ae_restrict_iff' hs.compl).mpr
    filter_upwards [(ae_restrict_iff' (ht n).compl).mp (hz n)] with x hx hxs
    exact hx (fun hxt => hxs (mem_iUnion.mpr ⟨n, hxt⟩))
  exact ⟨LinearIsometryEquiv.ofSurjective (zeroExtendL2 hs) hsurj,
    zeroExtendL2_modEq hs⟩

theorem AtomlessMeasure.restrict (hμ : AtomlessMeasure μ) (hs : MeasurableSet s) :
    AtomlessMeasure (μ.restrict s) := by
  intro a ha hp
  rw [Measure.restrict_apply ha] at hp
  obtain ⟨t, hts, ht, htp, hsp⟩ := hμ (a ∩ s) (ha.inter hs) hp
  refine ⟨t, fun x hx => (hts hx).1, ht, ?_, ?_⟩
  · rwa [Measure.restrict_apply ht, Set.inter_eq_left.mpr (fun x hx => (hts hx).2)]
  · rw [Measure.restrict_apply (ha.diff ht)]
    have he : (a \ t) ∩ s = (a ∩ s) \ t := by ext; simp only [mem_inter_iff, Set.mem_sdiff]; tauto
    rwa [he]

end OperatorPhaseRetrieval

end
