module

public import OperatorPhaseRetrieval.FiniteHaarStability
public import OperatorPhaseRetrieval.CoordinateStability

@[expose] public section

/-!
# Uniform finite-dimensional stability

The stability estimate is proved for five independent canonical Haar unitaries.
The event quantifies the chosen family before all pairs of vectors.
Its measurability, the exact success-probability bound, and existence are proved.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace OperatorPhaseRetrieval

variable {ι : Type*} [Fintype ι]

def coordinateStableFamily (c : ℝ) (U : Fin 5 → HaarUnitary (EuclideanSpace ℂ ι)) : Prop :=
  ∀ f g : EuclideanSpace ℂ ι, ∃ j,
    c * phaseDistance f g ≤ pairModulusDistance (U j) (WithLp.toLp 2 (f, g))

theorem coordinateStableFamily_isClosed (c : ℝ) :
    IsClosed {U : Fin 5 → HaarUnitary (EuclideanSpace ℂ ι) | coordinateStableFamily c U} := by
  have he : {U : Fin 5 → HaarUnitary (EuclideanSpace ℂ ι) | coordinateStableFamily c U} =
      ⋂ f : EuclideanSpace ℂ ι, ⋂ g : EuclideanSpace ℂ ι, ⋃ j : Fin 5,
        {U : Fin 5 → HaarUnitary (EuclideanSpace ℂ ι) | c * phaseDistance f g ≤ pairModulusDistance (U j) (WithLp.toLp 2 (f, g))} := by
    ext U
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, coordinateStableFamily]
  rw [he]
  apply isClosed_iInter
  intro f
  apply isClosed_iInter
  intro g
  apply isClosed_iUnion_of_finite
  intro j
  have hc : Continuous (fun U : Fin 5 → HaarUnitary (EuclideanSpace ℂ ι) =>
      (U j : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)) :=
    continuous_subtype_val.comp (continuous_apply j)
  have hd : Continuous (fun U : Fin 5 → HaarUnitary (EuclideanSpace ℂ ι) =>
      pairModulusDistance (U j) (WithLp.toLp 2 (f, g))) := by
    change Continuous (fun U : Fin 5 → HaarUnitary (EuclideanSpace ℂ ι) =>
      dist (coordinateModulus ((U j : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) f))
        (coordinateModulus ((U j : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) g)))
    exact (coordinateModulus_continuous.comp (hc.clm_apply continuous_const)).dist
      (coordinateModulus_continuous.comp (hc.clm_apply continuous_const))
  exact isClosed_le continuous_const hd

theorem coordinateStableFamily_measurableSet (c : ℝ) :
    MeasurableSet {U : Fin 5 → HaarUnitary (EuclideanSpace ℂ ι) | coordinateStableFamily c U} :=
  (coordinateStableFamily_isClosed c).measurableSet

theorem coordinateStableFamily_of_normalized
    (U : Fin 5 → HaarUnitary (EuclideanSpace ℂ ι)) (c : ℝ)
    (hU : ∀ p ∈ normalizedOrthogonalPairs, ∃ j, c ≤ pairModulusDistance (U j) p) :
    coordinateStableFamily c U := coordinateStability_of_normalized U c hU

theorem coordinate_stability_failure_subset (c : ℝ) :
    {U : Fin 5 → HaarUnitary (EuclideanSpace ℂ ι) | ¬ coordinateStableFamily c U} ⊆
      {U | ∃ p ∈ normalizedOrthogonalPairs, ∀ j, pairModulusDistance (U j) p < c} := by
  classical
  intro U hU
  by_contra! h
  apply hU
  apply coordinateStableFamily_of_normalized U c
  intro p hp
  by_contra! hbad
  exact h ⟨p, hp, hbad⟩

/-- The bad families have probability at most `2^(1485-32n)`.
The family is quantified before all pairs of vectors, so this is uniform stability. -/
theorem haarFive_stability_failure_le (hn : 50 ≤ Fintype.card ι) :
    (haarFiveProbability ι : Measure (Fin 5 → HaarUnitary (EuclideanSpace ℂ ι)))
      {U | ¬ coordinateStableFamily ((2 : ℝ) ^ (-100 : ℤ)) U} ≤
      ENNReal.ofReal ((2 : ℝ) ^ (1485 - 32 * (Fintype.card ι : ℤ))) :=
  (measure_mono (coordinate_stability_failure_subset ((2 : ℝ) ^ (-100 : ℤ)))).trans
    (haarFive_normalized_failure_dyadic hn)

/-- The success-probability formulation of the finite-dimensional stability estimate. -/
theorem haarFive_stability_probability (hn : 50 ≤ Fintype.card ι) :
    1 - ENNReal.ofReal ((2 : ℝ) ^ (1485 - 32 * (Fintype.card ι : ℤ))) ≤
      (haarFiveProbability ι : Measure (Fin 5 → HaarUnitary (EuclideanSpace ℂ ι)))
        {U | coordinateStableFamily ((2 : ℝ) ^ (-100 : ℤ)) U} := by
  let μ : Measure (Fin 5 → HaarUnitary (EuclideanSpace ℂ ι)) := haarFiveProbability ι
  let A : Set (Fin 5 → HaarUnitary (EuclideanSpace ℂ ι)) :=
    {U | coordinateStableFamily ((2 : ℝ) ^ (-100 : ℤ)) U}
  have hfail : μ Aᶜ ≤ ENNReal.ofReal ((2 : ℝ) ^ (1485 - 32 * (Fintype.card ι : ℤ))) :=
    haarFive_stability_failure_le hn
  apply tsub_le_iff_right.mpr
  calc
    (1 : ℝ≥0∞) = μ univ := (measure_univ : μ univ = 1).symm
    _ = μ (A ∪ Aᶜ) := by rw [union_compl_self]
    _ ≤ μ A + μ Aᶜ := measure_union_le A Aᶜ
    _ ≤ _ := add_le_add le_rfl hfail

theorem exists_five_stable_finite (hn : 50 ≤ Fintype.card ι) :
    ∃ U : Fin 5 → HaarUnitary (EuclideanSpace ℂ ι),
      coordinateStableFamily ((2 : ℝ) ^ (-100 : ℤ)) U := by
  obtain ⟨U, hU⟩ := exists_five_normalized_stable hn
  exact ⟨U, coordinateStableFamily_of_normalized U _ hU⟩

end OperatorPhaseRetrieval

end
