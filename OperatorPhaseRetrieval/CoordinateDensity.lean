import OperatorPhaseRetrieval.L2Density
import OperatorPhaseRetrieval.LimitCoordinates

/-!
# Density of the coordinate family

The algebraic identities of the formal expressions force their coordinate range
to be dense. Rational complex coefficients suffice, by continuity of scalar
multiplication and density of the rationals in the reals.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace OperatorPhaseRetrieval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Closure of a set stable under addition and rational complex scalars is a
complex submodule. -/
def rationalComplexClosure (S : Set E) (h0 : (0 : E) ∈ S)
    (ha : ∀ f ∈ S, ∀ g ∈ S, f + g ∈ S)
    (hs : ∀ a b : ℚ, ∀ f ∈ S, rationalComplex a b • f ∈ S) : Submodule ℂ E where
  carrier := closure S
  zero_mem' := subset_closure h0
  add_mem' := fun hf hg => map_mem_closure₂ continuous_add hf hg ha
  smul_mem' := by
    intro c f hf
    have hr (a b : ℚ) : rationalComplex a b • f ∈ closure S :=
      map_mem_closure (continuous_const_smul _) hf (hs a b)
    have h := map_mem_closure₂
      (f := fun a b : ℝ => ((a : ℂ) + (b : ℂ) * Complex.I) • f)
      (u := closure S)
      ((Complex.continuous_ofReal.comp continuous_fst).add
        ((Complex.continuous_ofReal.comp continuous_snd).mul_const Complex.I) |>.smul continuous_const)
      (Rat.denseRange_cast c.re) (Rat.denseRange_cast c.im)
      (by
        rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
        simpa only [rationalComplex, Complex.ofReal_ratCast] using hr a b)
    simpa only [Complex.re_add_im, closure_closure] using h

/-- The countable-expression density argument. Its hypotheses are exactly the
coordinate identities supplied by constants, addition, rational scalar
multiplication, conjugation, and modulus. -/
theorem denseRange_of_coordinate_algebra {ι : Type*} [Nonempty ι]
    (ν : Measure (ι → ℂ)) [IsFiniteMeasure ν] (f : ι → L2 ν)
    (hfae : ∀ i, (f i : (ι → ℂ) → ℂ) =ᵐ[ν] (fun z => z i))
    (h1 : Lp.const 2 ν (1 : ℂ) ∈ range f)
    (ha : ∀ i j, f i + f j ∈ range f)
    (hs : ∀ a b : ℚ, ∀ i, rationalComplex a b • f i ∈ range f)
    (hc : ∀ i, conjugateL2 (f i) ∈ range f)
    (hm : ∀ i, complexModulusL2 (f i) ∈ range f) : DenseRange f := by
  have h0 : (0 : L2 ν) ∈ range f := by
    simpa [rationalComplex] using hs 0 0 (Classical.arbitrary ι)
  let H := rationalComplexClosure (range f) h0
    (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact ha i j)
    (by rintro a b _ ⟨i, rfl⟩; exact hs a b i)
  have hH : IsClosed (H : Set (L2 ν)) := isClosed_closure
  have hconj : ∀ g ∈ H, conjugateL2 g ∈ H := by
    intro g hg
    exact map_mem_closure (Complex.isometry_conj.lipschitz.continuous_compLp (map_zero _))
      hg (by rintro _ ⟨i, rfl⟩; exact hc i)
  have hmod : ∀ g ∈ H, complexModulusL2 g ∈ H := by
    intro g hg
    exact map_mem_closure (lipschitz_complex_modulus.continuous_compLp (by simp))
      hg (by rintro _ ⟨i, rfl⟩; exact hm i)
  have htop : H = ⊤ := submodule_eq_top_of_coordinates ν H hH (subset_closure h1)
    hconj hmod f (fun i => subset_closure (mem_range_self i)) hfae
  intro g
  change g ∈ H
  rw [htop]
  trivial

/-- Coordinate identities imply the density needed by the limiting-unitary theorem. -/
theorem jointCoordinate_denseRange (ν : Measure (ℕ → ℂ)) [IsFiniteMeasure ν]
    (h : ∀ r, MemLp (fun z : ℕ → ℂ => z r) 2 ν)
    (h1 : Lp.const 2 ν (1 : ℂ) ∈ range (jointCoordinate ν h))
    (ha : ∀ r s, jointCoordinate ν h r + jointCoordinate ν h s ∈ range (jointCoordinate ν h))
    (hs : ∀ a b : ℚ, ∀ r,
      rationalComplex a b • jointCoordinate ν h r ∈ range (jointCoordinate ν h))
    (hc : ∀ r, conjugateL2 (jointCoordinate ν h r) ∈ range (jointCoordinate ν h))
    (hm : ∀ r, complexModulusL2 (jointCoordinate ν h r) ∈ range (jointCoordinate ν h)) :
    DenseRange (jointCoordinate ν h) :=
  denseRange_of_coordinate_algebra ν (jointCoordinate ν h)
    (jointCoordinate_coeFn ν h) h1 ha hs hc hm

/-- Indices of the elementary formal-expression operations. -/
structure CoordinateOperations where
  one : ℕ
  add : ℕ → ℕ → ℕ
  smul : ℚ → ℚ → ℕ → ℕ
  conj : ℕ → ℕ
  modulus : ℕ → ℕ

/-- Actual almost-everywhere algebraic identities of a coordinate law. -/
structure CoordinateAlgebraLaws (ops : CoordinateOperations) (ν : Measure (ℕ → ℂ)) : Prop where
  one : ∀ᵐ z ∂ν, z ops.one = 1
  add : ∀ r s, ∀ᵐ z ∂ν, z (ops.add r s) = z r + z s
  smul : ∀ a b r, ∀ᵐ z ∂ν, z (ops.smul a b r) = rationalComplex a b * z r
  conj : ∀ r, ∀ᵐ z ∂ν, z (ops.conj r) = star (z r)
  modulus : ∀ r, ∀ᵐ z ∂ν, z (ops.modulus r) = (‖z r‖ : ℂ)

/-- All the elementary expression identities survive weak convergence. -/
theorem CoordinateAlgebraLaws.weakLimit (ops : CoordinateOperations)
    {P : ℕ → ProbabilityMeasure (ℕ → ℂ)} {Q : ProbabilityMeasure (ℕ → ℂ)}
    (hlim : Filter.Tendsto P Filter.atTop (𝓝 Q))
    (h : ∀ n, CoordinateAlgebraLaws ops (P n : Measure (ℕ → ℂ))) :
    CoordinateAlgebraLaws ops (Q : Measure (ℕ → ℂ)) where
  one := jointLaw_limit_ae_eq hlim _ _ (continuous_apply ops.one) continuous_const (fun n => (h n).one)
  add r s := jointLaw_limit_ae_eq hlim _ _ (continuous_apply (ops.add r s))
    ((continuous_apply r).add (continuous_apply s)) (fun n => (h n).add r s)
  smul a b r := jointLaw_limit_ae_eq hlim _ _ (continuous_apply (ops.smul a b r))
    (continuous_const.mul (continuous_apply r)) (fun n => (h n).smul a b r)
  conj r := jointLaw_limit_ae_eq hlim _ _ (continuous_apply (ops.conj r))
    ((continuous_apply r).star) (fun n => (h n).conj r)
  modulus r := jointLaw_limit_ae_eq hlim _ _ (continuous_apply (ops.modulus r))
    (Complex.continuous_ofReal.comp (continuous_apply r).norm) (fun n => (h n).modulus r)

/-- The formal-expression identities prove coordinate density without an additional
density hypothesis. -/
theorem CoordinateAlgebraLaws.denseRange {ops : CoordinateOperations}
    {ν : Measure (ℕ → ℂ)} [IsFiniteMeasure ν]
    (laws : CoordinateAlgebraLaws ops ν)
    (h : ∀ r, MemLp (fun z : ℕ → ℂ => z r) 2 ν) : DenseRange (jointCoordinate ν h) := by
  apply jointCoordinate_denseRange ν h
  · refine ⟨ops.one, ?_⟩
    apply Lp.ext
    filter_upwards [jointCoordinate_coeFn ν h ops.one, Lp.coeFn_const 2 ν (1 : ℂ), laws.one]
      with z hz hc ho
    exact hz.trans (ho.trans hc.symm)
  · intro r s
    refine ⟨ops.add r s, ?_⟩
    apply Lp.ext
    filter_upwards [jointCoordinate_coeFn ν h (ops.add r s), jointCoordinate_coeFn ν h r,
      jointCoordinate_coeFn ν h s, Lp.coeFn_add (jointCoordinate ν h r) (jointCoordinate ν h s),
      laws.add r s] with z hz hr hs ha he
    simp only [Pi.add_apply] at ha
    rw [hz, ha, hr, hs, he]
  · intro a b r
    refine ⟨ops.smul a b r, ?_⟩
    apply Lp.ext
    filter_upwards [jointCoordinate_coeFn ν h (ops.smul a b r), jointCoordinate_coeFn ν h r,
      Lp.coeFn_smul (rationalComplex a b) (jointCoordinate ν h r), laws.smul a b r]
      with z hz hr hs he
    simp only [Pi.smul_apply] at hs
    rw [hz, hs, hr, he, smul_eq_mul]
  · intro r
    refine ⟨ops.conj r, ?_⟩
    apply Lp.ext
    filter_upwards [jointCoordinate_coeFn ν h (ops.conj r), jointCoordinate_coeFn ν h r,
      conjugateL2_coeFn (jointCoordinate ν h r), laws.conj r] with z hz hr hc he
    rw [hz, hc, hr, he]
  · intro r
    refine ⟨ops.modulus r, ?_⟩
    apply Lp.ext
    filter_upwards [jointCoordinate_coeFn ν h (ops.modulus r), jointCoordinate_coeFn ν h r,
      complexModulusL2_coeFn (jointCoordinate ν h r), laws.modulus r] with z hz hr hm he
    rw [hz, hm, hr, he]

end OperatorPhaseRetrieval

end
