module

public import OperatorPhaseRetrieval.ExpressionBounds

@[expose] public section

/-!
# Density from constants, conjugation, and modulus

Analytic ingredients for the coordinate-density argument of the limit construction.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace OperatorPhaseRetrieval

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Bounded almost-everywhere convergence implies convergence in `L²` on a finite measure space. -/
theorem l2_tendsto_of_ae_tendsto_of_bound [IsFiniteMeasure μ] (f : ℕ → L2 μ) (g : L2 μ) (B : ℝ)
    (hf : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ B) (hg : ∀ᵐ x ∂μ, ‖g x‖ ≤ B)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto f atTop (𝓝 g) := by
  have hi : Tendsto (fun n => ∫ x, ‖f n x - g x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun n x => ‖f n x - g x‖ ^ 2) (f := fun _ => (0 : ℝ))
      (fun _ => (2 * B) ^ 2)
      (fun n => ((Lp.aestronglyMeasurable (f n)).sub (Lp.aestronglyMeasurable g)).norm.pow 2)
      (integrable_const _)
      (fun n => ?_) ?_
    · simpa using h
    · filter_upwards [hf n, hg] with x hx hy
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hB : 0 ≤ 2 * B := by linarith [norm_nonneg (g x)]
      have hfg := (norm_sub_le (f n x) (g x)).trans (add_le_add hx hy)
      nlinarith [norm_nonneg (f n x - g x)]
    · filter_upwards [hlim] with x hx
      simpa using ((hx.sub_const (g x)).norm.pow 2)
  have he (n : ℕ) : ‖f n - g‖ ^ 2 = ∫ x, ‖f n x - g x‖ ^ 2 ∂μ := by
    rw [l2_norm_sq_integral]
    exact integral_congr_ae ((Lp.coeFn_sub (f n) g).fun_comp (fun z : ℂ => ‖z‖ ^ 2))
  have hn : Tendsto (fun n => ‖f n - g‖) atTop (𝓝 0) := by
    simpa only [← he, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hi.sqrt
  exact tendsto_iff_dist_tendsto_zero.mpr (by simpa only [dist_eq_norm] using hn)

/-- The real part, represented as a complex-valued `L²` function. -/
def realPartL2 (f : L2 μ) : L2 μ := (2 : ℂ)⁻¹ • (f + conjugateL2 f)

theorem realPartL2_coeFn (f : L2 μ) :
    (realPartL2 f : X → ℂ) =ᵐ[μ] (fun x => ((f x).re : ℂ)) := by
  filter_upwards [Lp.coeFn_smul (2 : ℂ)⁻¹ (f + conjugateL2 f),
    Lp.coeFn_add f (conjugateL2 f), conjugateL2_coeFn f] with x h1 h2 h3
  change ((2 : ℂ)⁻¹ • (f + conjugateL2 f)) x = _
  simp only [Pi.smul_apply, Pi.add_apply] at h1 h2
  rw [h1, h2, h3, smul_eq_mul]
  apply Complex.ext <;> simp
  ring

/-- Positive part on real-valued functions; defined everywhere in complex `L²`. -/
def positivePartL2 (f : L2 μ) : L2 μ := (2 : ℂ)⁻¹ • (f + complexModulusL2 f)

theorem positivePartL2_coeFn (f : L2 μ) (hreal : ∀ᵐ x ∂μ, (f x).im = 0) :
    (positivePartL2 f : X → ℂ) =ᵐ[μ] (fun x => ((max (f x).re 0 : ℝ) : ℂ)) := by
  filter_upwards [Lp.coeFn_smul (2 : ℂ)⁻¹ (f + complexModulusL2 f),
    Lp.coeFn_add f (complexModulusL2 f), complexModulusL2_coeFn f, hreal]
    with x h1 h2 h3 hx
  change ((2 : ℂ)⁻¹ • (f + complexModulusL2 f)) x = _
  simp only [Pi.smul_apply, Pi.add_apply] at h1 h2
  rw [h1, h2, h3, smul_eq_mul]
  have he : f x = ((f x).re : ℂ) := by apply Complex.ext <;> simp [hx]
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  apply Complex.ext <;> simp
  by_cases h : 0 ≤ (f x).re
  · rw [abs_of_nonneg h, max_eq_left h]
    ring
  · rw [abs_of_nonpos (le_of_not_ge h), max_eq_right (le_of_not_ge h)]
    ring

/-- Minimum on real-valued functions, expressed using vector operations and modulus. -/
def minimumL2 (f g : L2 μ) : L2 μ := f - positivePartL2 (f - g)

theorem minimumL2_coeFn (f g : L2 μ)
    (hf : ∀ᵐ x ∂μ, (f x).im = 0) (hg : ∀ᵐ x ∂μ, (g x).im = 0) :
    (minimumL2 f g : X → ℂ) =ᵐ[μ]
      (fun x => ((min (f x).re (g x).re : ℝ) : ℂ)) := by
  have hr : ∀ᵐ x ∂μ, ((f - g : L2 μ) x).im = 0 := by
    filter_upwards [Lp.coeFn_sub f g, hf, hg] with x hx hfx hgx
    simp only [Pi.sub_apply] at hx
    rw [hx]
    simp only [Complex.sub_im, hfx, hgx, sub_self]
  filter_upwards [Lp.coeFn_sub f (positivePartL2 (f - g)),
    positivePartL2_coeFn (f - g) hr, Lp.coeFn_sub f g, hf] with x h1 h2 h3 hfx
  change (f - positivePartL2 (f - g)) x = _
  simp only [Pi.sub_apply] at h1 h3
  rw [h1, h2, h3]
  apply Complex.ext <;> simp [hfx]
  rw [min_def, max_def]
  split_ifs <;> linarith

theorem realPartL2_mem (H : Submodule ℂ (L2 μ))
    (hc : ∀ f ∈ H, conjugateL2 f ∈ H) {f : L2 μ} (hf : f ∈ H) : realPartL2 f ∈ H :=
  H.smul_mem _ (H.add_mem hf (hc f hf))

theorem positivePartL2_mem (H : Submodule ℂ (L2 μ))
    (hm : ∀ f ∈ H, complexModulusL2 f ∈ H) {f : L2 μ} (hf : f ∈ H) :
    positivePartL2 f ∈ H := H.smul_mem _ (H.add_mem hf (hm f hf))

theorem minimumL2_mem (H : Submodule ℂ (L2 μ))
    (hm : ∀ f ∈ H, complexModulusL2 f ∈ H) {f g : L2 μ} (hf : f ∈ H) (hg : g ∈ H) :
    minimumL2 f g ∈ H := H.sub_mem hf (positivePartL2_mem H hm (H.sub_mem hf hg))

variable [IsFiniteMeasure μ]

/-- Bounded ramps converging to a real halfspace indicator. -/
def halfspaceRampL2 (f : L2 μ) (a : ℝ) (n : ℕ) : L2 μ :=
  minimumL2 (Lp.const 2 μ 1)
    ((n : ℂ) • positivePartL2 (realPartL2 f - Lp.const 2 μ (a : ℂ)))

theorem halfspaceRampL2_coeFn (f : L2 μ) (a : ℝ) (n : ℕ) :
    (halfspaceRampL2 f a n : X → ℂ) =ᵐ[μ]
      (fun x => ((min 1 ((n : ℝ) * max ((f x).re - a) 0) : ℝ) : ℂ)) := by
  have h1 : ⇑(realPartL2 f - Lp.const 2 μ (a : ℂ) : L2 μ) =ᵐ[μ]
      (fun x => (((f x).re - a : ℝ) : ℂ)) := by
    filter_upwards [Lp.coeFn_sub (realPartL2 f) (Lp.const 2 μ (a : ℂ)),
      realPartL2_coeFn f, Lp.coeFn_const 2 μ (a : ℂ)] with x hx hfx hax
    simp only [Pi.sub_apply, Function.const_apply] at hx hax
    rw [hx, hfx, hax, Complex.ofReal_sub]
  have h2 := positivePartL2_coeFn (realPartL2 f - Lp.const 2 μ (a : ℂ))
    (h1.mono fun x hx => by rw [hx]; exact Complex.ofReal_im _)
  have h3 : ⇑((n : ℂ) • positivePartL2 (realPartL2 f - Lp.const 2 μ (a : ℂ)) : L2 μ)
      =ᵐ[μ] (fun x => (((n : ℝ) * max ((f x).re - a) 0 : ℝ) : ℂ)) := by
    filter_upwards [Lp.coeFn_smul (n : ℂ)
      (positivePartL2 (realPartL2 f - Lp.const 2 μ (a : ℂ))), h2, h1] with x hx hy hz
    simp only [Pi.smul_apply] at hx
    rw [hx, hy, hz]
    simp only [Complex.ofReal_re, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_natCast]
  have h4 := minimumL2_coeFn (Lp.const 2 μ 1) _
    ((Lp.coeFn_const 2 μ (1 : ℂ)).mono fun x hx => by rw [hx]; rfl)
    (h3.mono fun x hx => by rw [hx]; exact Complex.ofReal_im _)
  filter_upwards [h4, Lp.coeFn_const 2 μ (1 : ℂ), h3] with x hx hy hz
  change (minimumL2 _ _) x = _
  rw [hx, hy, hz]
  simp only [Function.const_apply, Complex.one_re, Complex.ofReal_re]

theorem halfspaceRampL2_mem (H : Submodule ℂ (L2 μ))
    (h1 : Lp.const 2 μ (1 : ℂ) ∈ H)
    (hc : ∀ f ∈ H, conjugateL2 f ∈ H)
    (hm : ∀ f ∈ H, complexModulusL2 f ∈ H) {f : L2 μ} (hf : f ∈ H)
    (a : ℝ) (n : ℕ) : halfspaceRampL2 f a n ∈ H := by
  apply minimumL2_mem H hm h1
  apply H.smul_mem
  apply positivePartL2_mem H hm
  apply H.sub_mem (realPartL2_mem H hc hf)
  have he : Lp.const 2 μ (a : ℂ) = (a : ℂ) • Lp.const 2 μ (1 : ℂ) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_const 2 μ (a : ℂ), Lp.coeFn_const 2 μ (1 : ℂ),
      Lp.coeFn_smul (a : ℂ) (Lp.const 2 μ (1 : ℂ))] with x hx hy hz
    change (Lp.const 2 μ (a : ℂ)) x = ((a : ℂ) • Lp.const 2 μ (1 : ℂ)) x
    simp only [Pi.smul_apply, Function.const_apply] at hx hy hz
    rw [hx, hz, hy, smul_eq_mul, mul_one]
  rw [he]
  exact H.smul_mem _ h1

omit [MeasurableSpace X] [IsFiniteMeasure μ] in
theorem tendsto_halfspaceRamp (r a : ℝ) :
    Tendsto (fun n : ℕ => ((min 1 ((n : ℝ) * max (r - a) 0) : ℝ) : ℂ))
      atTop (𝓝 (if a < r then 1 else 0)) := by
  by_cases h : a < r
  · obtain ⟨N, hN⟩ := exists_nat_gt (1 / (r - a))
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hb : 1 ≤ (n : ℝ) * (r - a) := by
      have hp : 0 < r - a := sub_pos.mpr h
      have := (div_lt_iff₀ hp).mp hN
      nlinarith
    simp [h, max_eq_left (sub_pos.mpr h).le, min_eq_left hb]
  · simp [h, max_eq_right (sub_nonpos.mpr (le_of_not_gt h))]

/-- The indicator of a measurable set, with value one, in complex `L²`. -/
def unitIndicatorL2 {s : Set X} (hs : MeasurableSet s) : L2 μ :=
  indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℂ)

theorem unitIndicatorL2_coeFn {s : Set X} (hs : MeasurableSet s) :
    (unitIndicatorL2 (μ := μ) hs : X → ℂ) =ᵐ[μ] s.indicator (fun _ => (1 : ℂ)) :=
  indicatorConstLp_coeFn

theorem unitIndicatorL2_norm_bound {s : Set X} (hs : MeasurableSet s) :
    ∀ᵐ x ∂μ, ‖unitIndicatorL2 (μ := μ) hs x‖ ≤ 1 := by
  filter_upwards [unitIndicatorL2_coeFn (μ := μ) hs] with x hx
  rw [hx]
  by_cases h : x ∈ s <;> simp [h]

theorem unitIndicatorL2_real {s : Set X} (hs : MeasurableSet s) :
    ∀ᵐ x ∂μ, (unitIndicatorL2 (μ := μ) hs x).im = 0 := by
  filter_upwards [unitIndicatorL2_coeFn (μ := μ) hs] with x hx
  rw [hx]
  by_cases h : x ∈ s <;> simp [h]

/-- Closed subspaces containing constants and closed under conjugation and modulus
contain indicators of real halfspaces of any represented measurable function. -/
theorem unitIndicatorL2_halfspace_mem (H : Submodule ℂ (L2 μ))
    (hH : IsClosed (H : Set (L2 μ))) (h1 : Lp.const 2 μ (1 : ℂ) ∈ H)
    (hc : ∀ f ∈ H, conjugateL2 f ∈ H)
    (hm : ∀ f ∈ H, complexModulusL2 f ∈ H)
    (u : X → ℂ) (hu : Measurable u) (f : L2 μ) (hf : f ∈ H)
    (hfu : (f : X → ℂ) =ᵐ[μ] u) (a : ℝ) :
    unitIndicatorL2 (μ := μ) (s := {x | a < (u x).re})
      (measurableSet_lt measurable_const (Complex.measurable_re.comp hu)) ∈ H := by
  let hs : MeasurableSet {x | a < (u x).re} := measurableSet_lt measurable_const (Complex.measurable_re.comp hu)
  have hlim : Tendsto (halfspaceRampL2 f a) atTop (𝓝 (unitIndicatorL2 (μ := μ) hs)) := by
    apply l2_tendsto_of_ae_tendsto_of_bound _ _ 1
    · intro n
      filter_upwards [halfspaceRampL2_coeFn f a n] with x hx
      rw [hx, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (le_min (by norm_num) (by positivity))]
      exact min_le_left _ _
    · exact unitIndicatorL2_norm_bound hs
    · filter_upwards [ae_all_iff.mpr (fun n => halfspaceRampL2_coeFn f a n),
        unitIndicatorL2_coeFn (μ := μ) hs, hfu] with x hx hi hfx
      simp only [hx, hfx]
      rw [hi]
      simpa only [Set.indicator_apply, mem_ofPred_eq] using tendsto_halfspaceRamp (u x).re a
  exact hH.mem_of_tendsto hlim (Eventually.of_forall (halfspaceRampL2_mem H h1 hc hm hf a))

theorem unitIndicatorL2_compl {s : Set X} (hs : MeasurableSet s) :
    unitIndicatorL2 (μ := μ) hs.compl = Lp.const 2 μ 1 - unitIndicatorL2 hs := by
  apply Lp.ext
  filter_upwards [unitIndicatorL2_coeFn (μ := μ) hs.compl, unitIndicatorL2_coeFn (μ := μ) hs,
    Lp.coeFn_const 2 μ (1 : ℂ), Lp.coeFn_sub (Lp.const 2 μ 1) (unitIndicatorL2 hs)]
    with x h1 h2 h3 h4
  change unitIndicatorL2 hs.compl x = (Lp.const 2 μ 1 - unitIndicatorL2 hs : L2 μ) x
  simp only [Pi.sub_apply, Function.const_apply] at h4 h3
  rw [h1, h4, h3, h2]
  by_cases hx : x ∈ s <;> simp [hx]

theorem unitIndicatorL2_inter {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    unitIndicatorL2 (μ := μ) (hs.inter ht) = minimumL2 (unitIndicatorL2 hs) (unitIndicatorL2 ht) := by
  apply Lp.ext
  filter_upwards [unitIndicatorL2_coeFn (μ := μ) (hs.inter ht),
    unitIndicatorL2_coeFn (μ := μ) hs, unitIndicatorL2_coeFn (μ := μ) ht,
    minimumL2_coeFn (unitIndicatorL2 hs) (unitIndicatorL2 ht)
      (unitIndicatorL2_real hs) (unitIndicatorL2_real ht)] with x h1 h2 h3 h4
  change unitIndicatorL2 (hs.inter ht) x = minimumL2 (unitIndicatorL2 hs) (unitIndicatorL2 ht) x
  rw [h1, h4, h2, h3]
  by_cases hx : x ∈ s <;> by_cases hy : x ∈ t <;> simp [hx, hy]

theorem unitIndicatorL2_iUnion_tendsto (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
    (hmono : Monotone s) :
    Tendsto (fun n => unitIndicatorL2 (μ := μ) (hs n)) atTop
      (𝓝 (unitIndicatorL2 (MeasurableSet.iUnion hs))) := by
  apply l2_tendsto_of_ae_tendsto_of_bound _ _ 1
  · exact fun n => unitIndicatorL2_norm_bound (hs n)
  · exact unitIndicatorL2_norm_bound _
  · filter_upwards [ae_all_iff.mpr (fun n => unitIndicatorL2_coeFn (μ := μ) (hs n)),
      unitIndicatorL2_coeFn (μ := μ) (MeasurableSet.iUnion hs)] with x hx hU
    simp only [hx, hU]
    by_cases h : x ∈ ⋃ n, s n
    · obtain ⟨N, hN⟩ := mem_iUnion.mp h
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with n hn
      simp only [Set.indicator_of_mem h, Set.indicator_of_mem (hmono hn hN)]
    · have hn (n : ℕ) : x ∉ s n := fun hnx => h (mem_iUnion.mpr ⟨n, hnx⟩)
      simp only [Set.indicator_of_notMem h, Set.indicator_of_notMem (hn _)]
      exact tendsto_const_nhds

/-- A closed complex subspace containing every measurable unit indicator is all of `L²`. -/
theorem submodule_eq_top_of_unitIndicators (H : Submodule ℂ (L2 μ))
    (hH : IsClosed (H : Set (L2 μ)))
    (hi : ∀ (s : Set X) (hs : MeasurableSet s), unitIndicatorL2 (μ := μ) hs ∈ H) : H = ⊤ := by
  apply top_unique
  intro f _
  refine Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (fun f : L2 μ => f ∈ H) ?_ ?_ hH f
  · intro c s hs hμs
    have he : (Lp.simpleFunc.indicatorConst 2 hs hμs.ne c : L2 μ) = c • unitIndicatorL2 hs := by
      apply Lp.ext
      filter_upwards [@indicatorConstLp_coeFn X ℂ _ 2 μ _ s hs hμs.ne c,
        unitIndicatorL2_coeFn (μ := μ) hs, Lp.coeFn_smul c (unitIndicatorL2 (μ := μ) hs)]
        with x h1 h2 h3
      change (Lp.simpleFunc.indicatorConst 2 hs hμs.ne c : L2 μ) x = (c • unitIndicatorL2 hs : L2 μ) x
      simp only [Pi.smul_apply] at h3
      rw [h3, h2]
      by_cases hx : x ∈ s <;> simpa [hx] using h1
    rw [he]
    exact H.smul_mem c (hi s hs)
  · intro f g _ _ _ hf hg
    exact H.add_mem hf hg

theorem unitIndicatorL2_union_mem (H : Submodule ℂ (L2 μ))
    (hm : ∀ f ∈ H, complexModulusL2 f ∈ H)
    {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hsi : unitIndicatorL2 (μ := μ) hs ∈ H) (hti : unitIndicatorL2 (μ := μ) ht ∈ H) :
    unitIndicatorL2 (μ := μ) (hs.union ht) ∈ H := by
  have he : unitIndicatorL2 (μ := μ) (hs.union ht) =
      unitIndicatorL2 hs + unitIndicatorL2 ht - unitIndicatorL2 (hs.inter ht) := by
    apply Lp.ext
    filter_upwards [unitIndicatorL2_coeFn (μ := μ) (hs.union ht),
      unitIndicatorL2_coeFn (μ := μ) hs, unitIndicatorL2_coeFn (μ := μ) ht,
      unitIndicatorL2_coeFn (μ := μ) (hs.inter ht),
      Lp.coeFn_add (unitIndicatorL2 (μ := μ) hs) (unitIndicatorL2 ht),
      Lp.coeFn_sub (unitIndicatorL2 (μ := μ) hs + unitIndicatorL2 ht) (unitIndicatorL2 (hs.inter ht))]
      with x h1 h2 h3 h4 h5 h6
    change unitIndicatorL2 (hs.union ht) x =
      (unitIndicatorL2 hs + unitIndicatorL2 ht - unitIndicatorL2 (hs.inter ht) : L2 μ) x
    simp only [Pi.add_apply, Pi.sub_apply] at h5 h6
    rw [h1, h6, h5, h2, h3, h4]
    by_cases hx : x ∈ s <;> by_cases hy : x ∈ t <;> simp [hx, hy]
  rw [he, unitIndicatorL2_inter hs ht]
  exact H.sub_mem (H.add_mem hsi hti) (minimumL2_mem H hm hsi hti)

theorem unitIndicatorL2_iUnion_mem (H : Submodule ℂ (L2 μ))
    (hH : IsClosed (H : Set (L2 μ))) (hm : ∀ f ∈ H, complexModulusL2 f ∈ H)
    (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
    (hsi : ∀ n, unitIndicatorL2 (μ := μ) (hs n) ∈ H) :
    unitIndicatorL2 (μ := μ) (MeasurableSet.iUnion hs) ∈ H := by
  let t (n : ℕ) : Set X := ⋃ i ∈ Finset.range n, s i
  have ht (n : ℕ) : MeasurableSet (t n) :=
    (Finset.range n).measurableSet_biUnion (fun i _ => hs i)
  have hti (n : ℕ) : unitIndicatorL2 (μ := μ) (ht n) ∈ H := by
    induction n with
    | zero => simp [t, unitIndicatorL2]
    | succ n hn =>
      have he : t (n + 1) = t n ∪ s n := by
        simp only [t, Finset.range_add_one, Finset.mem_insert,
          iUnion_iUnion_eq_or_left, union_comm]
      have hi := unitIndicatorL2_union_mem H hm (ht n) (hs n) hn (hsi n)
      simpa only [he] using hi
  have htmono : Monotone t := by
    intro n m hnm
    exact biUnion_subset_biUnion_left (Finset.range_mono hnm)
  have he : (⋃ n, t n) = ⋃ n, s n := by
    ext x
    simp only [t, mem_iUnion, Finset.mem_range]
    constructor
    · rintro ⟨n, i, _, hi⟩
      exact ⟨i, hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i + 1, i, Nat.lt_succ_self i, hi⟩
  have hlim := unitIndicatorL2_iUnion_tendsto (μ := μ) t ht htmono
  have hi := hH.mem_of_tendsto hlim (Eventually.of_forall hti)
  have heI : unitIndicatorL2 (μ := μ) (MeasurableSet.iUnion ht) =
      unitIndicatorL2 (MeasurableSet.iUnion hs) := by
    congr 1
  rwa [heI] at hi

/-- Measurable sets whose unit indicators belong to a closed modulus-stable subspace
form a sigma algebra. -/
@[instance_reducible]
def indicatorMeasurableSpace (H : Submodule ℂ (L2 μ))
    (hH : IsClosed (H : Set (L2 μ))) (h1 : Lp.const 2 μ (1 : ℂ) ∈ H)
    (hm : ∀ f ∈ H, complexModulusL2 f ∈ H) : MeasurableSpace X where
  MeasurableSet' s := ∃ hs : MeasurableSet s, unitIndicatorL2 (μ := μ) hs ∈ H
  measurableSet_empty := ⟨MeasurableSet.empty, by simp [unitIndicatorL2]⟩
  measurableSet_compl := by
    rintro s ⟨hs, hi⟩
    exact ⟨hs.compl, by rw [unitIndicatorL2_compl hs]; exact H.sub_mem h1 hi⟩
  measurableSet_iUnion := by
    intro s hs
    choose hsm hsi using hs
    exact ⟨MeasurableSet.iUnion hsm, unitIndicatorL2_iUnion_mem H hH hm s hsm hsi⟩

/-- Real and imaginary halfspaces of represented functions are measurable for the
sigma algebra determined by the closed subspace. -/
theorem measurable_indicatorMeasurableSpace (H : Submodule ℂ (L2 μ))
    (hH : IsClosed (H : Set (L2 μ))) (h1 : Lp.const 2 μ (1 : ℂ) ∈ H)
    (hc : ∀ f ∈ H, conjugateL2 f ∈ H)
    (hm : ∀ f ∈ H, complexModulusL2 f ∈ H)
    (u : X → ℂ) (hu : Measurable u) (f : L2 μ) (hf : f ∈ H)
    (hfu : (f : X → ℂ) =ᵐ[μ] u) :
    @Measurable X ℂ (indicatorMeasurableSpace H hH h1 hm) inferInstance u := by
  have hre : @Measurable X ℝ (indicatorMeasurableSpace H hH h1 hm) inferInstance
      (fun x => (u x).re) := by
    apply measurable_of_Ioi
    intro a
    exact ⟨measurableSet_lt measurable_const (Complex.measurable_re.comp hu),
      unitIndicatorL2_halfspace_mem H hH h1 hc hm u hu f hf hfu a⟩
  have hui : Measurable (fun x => -Complex.I * u x) := measurable_const.mul hu
  have hfi : ((-Complex.I) • f : L2 μ) =ᵐ[μ] (fun x => -Complex.I * u x) := by
    filter_upwards [Lp.coeFn_smul (-Complex.I) f, hfu] with x hx hy
    simpa only [Pi.smul_apply, hy, smul_eq_mul] using hx
  have him : @Measurable X ℝ (indicatorMeasurableSpace H hH h1 hm) inferInstance
      (fun x => (u x).im) := by
    have hi : @Measurable X ℝ (indicatorMeasurableSpace H hH h1 hm) inferInstance
        (fun x => (-Complex.I * u x).re) := by
      apply measurable_of_Ioi
      intro a
      exact ⟨measurableSet_lt measurable_const (Complex.measurable_re.comp hui),
        unitIndicatorL2_halfspace_mem H hH h1 hc hm _ hui _ (H.smul_mem _ hf) hfi a⟩
    simpa using hi
  have hm' := (Complex.measurable_ofReal.comp hre).add
    ((Complex.measurable_ofReal.comp him).mul (measurable_const (a := Complex.I)))
  simpa only [Pi.add_def, Pi.mul_def, Function.comp_def, Complex.re_add_im] using hm'

omit [MeasurableSpace X] [IsFiniteMeasure μ] in
/-- On a complex product space, a closed subspace containing all coordinate functions
and constants, and closed under conjugation and modulus, is the whole `L²` space. -/
theorem submodule_eq_top_of_coordinates {ι : Type*} (ν : Measure (ι → ℂ)) [IsFiniteMeasure ν]
    (H : Submodule ℂ (L2 ν)) (hH : IsClosed (H : Set (L2 ν)))
    (h1 : Lp.const 2 ν (1 : ℂ) ∈ H)
    (hc : ∀ f ∈ H, conjugateL2 f ∈ H)
    (hm : ∀ f ∈ H, complexModulusL2 f ∈ H)
    (f : ι → L2 ν) (hf : ∀ i, f i ∈ H)
    (hfae : ∀ i, (f i : (ι → ℂ) → ℂ) =ᵐ[ν] (fun z => z i)) : H = ⊤ := by
  have hcoord (i : ι) : @Measurable (ι → ℂ) ℂ (indicatorMeasurableSpace H hH h1 hm) Complex.measurableSpace (fun z => z i) :=
    measurable_indicatorMeasurableSpace H hH h1 hc hm _ (measurable_pi_apply i) _ (hf i) (hfae i)
  have hid : @Measurable (ι → ℂ) (ι → ℂ) (indicatorMeasurableSpace H hH h1 hm) MeasurableSpace.pi id :=
    by
      let : MeasurableSpace (ι → ℂ) := indicatorMeasurableSpace H hH h1 hm
      exact measurable_pi_iff.mpr hcoord
  apply submodule_eq_top_of_unitIndicators H hH
  intro s hs
  obtain ⟨hs', hi⟩ := hid hs
  exact hi

end OperatorPhaseRetrieval

end
