module

public import OperatorPhaseRetrieval.NormalizedEmpiricalLaw
public import OperatorPhaseRetrieval.FiniteGaussianSeed
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OperatorPhaseRetrieval

/-- Circular Gaussian with real and imaginary coordinate variance `1/2`. -/
def circularGaussian : ProbabilityMeasure ℂ :=
  scaledProbability ⟨stdGaussian ℂ, inferInstance⟩ (Real.sqrt 2)⁻¹

instance circularGaussian_nullSingletonClass :
    NullSingletonClass (circularGaussian : Measure ℂ) := by
  let := stdGaussian_nullSingletonClass (E := ℂ)
  constructor
  intro z
  change ((stdGaussian ℂ).map (fun x : ℂ => (Real.sqrt 2)⁻¹ • x)) {z} = 0
  have hm : Measurable (fun x : ℂ => (Real.sqrt 2)⁻¹ • x) :=
    (measurable_id.const_smul ((Real.sqrt 2)⁻¹ : ℝ))
  rw [Measure.map_apply hm (measurableSet_singleton z)]
  apply Set.Countable.measure_zero
  apply (Set.countable_singleton z).preimage
  exact smul_right_injective ℂ (by positivity : (Real.sqrt 2)⁻¹ ≠ 0)

/-- One common probability space carrying all independent Gaussian samples. -/
def iidComplexGaussian : Measure (ℕ → ℂ) :=
  Measure.infinitePi (fun _ : ℕ => stdGaussian ℂ)

instance iidComplexGaussian_isProbabilityMeasure : IsProbabilityMeasure iidComplexGaussian := by
  unfold iidComplexGaussian
  infer_instance

theorem iidComplexGaussian_coordinate (i : ℕ) :
    MeasurePreserving (fun z : ℕ → ℂ => z i) iidComplexGaussian (stdGaussian ℂ) :=
  measurePreserving_eval_infinitePi (fun _ : ℕ => stdGaussian ℂ) i

theorem iidComplexGaussian_independent :
    iIndepFun (fun i : ℕ => fun z : ℕ → ℂ => z i) iidComplexGaussian :=
  iIndepFun_infinitePi (X := fun (_ : ℕ) (z : ℂ) => z) (fun _ => measurable_id)

theorem iidComplexGaussian_identDistrib (i : ℕ) :
    IdentDistrib (fun z : ℕ → ℂ => z i) (fun z : ℕ → ℂ => z 0) iidComplexGaussian iidComplexGaussian where
  aemeasurable_fst := (measurable_pi_apply i).aemeasurable
  aemeasurable_snd := (measurable_pi_apply 0).aemeasurable
  map_eq := (iidComplexGaussian_coordinate i).map_eq.trans (iidComplexGaussian_coordinate 0).map_eq.symm

theorem iidComplexGaussian_prefix_law (n : ℕ) :
    iidComplexGaussian.map (fun z : ℕ → ℂ => fun i : Fin n => z i) =
      Measure.pi (fun _ : Fin n => stdGaussian ℂ) := by
  change (Measure.infinitePi (fun _ : ℕ => stdGaussian ℂ)).map _ = _
  rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective, Measure.infinitePi_eq_pi]

/-- Empirical laws of the normalized Gaussian samples converge weakly almost surely. -/
theorem normalizedGaussian_empiricalLaw_tendsto :
    ∀ᵐ z ∂iidComplexGaussian,
      Tendsto (fun n => empiricalLaw (fun i =>
        (Real.sqrt (empiricalAverage (fun y : ℂ => ‖y‖ ^ 2) z (n+1)))⁻¹ • z i) n)
        atTop (𝓝 circularGaussian) := by
  have hmem : MemLp (fun z : ℕ → ℂ => z 0) 2 iidComplexGaussian := by
    simpa only [Function.comp_def, id_eq] using
      (IsGaussian.memLp_two_id (μ := stdGaussian ℂ)).comp_measurePreserving
        (iidComplexGaussian_coordinate 0)
  have hmean : ∫ z, ‖z 0‖ ^ 2 ∂iidComplexGaussian = 2 := by
    have he := integral_map (μ := iidComplexGaussian) (measurable_pi_apply 0).aemeasurable
      (measurable_norm.pow_const 2).aestronglyMeasurable
    rw [(iidComplexGaussian_coordinate 0).map_eq] at he
    rw [← he]
    simpa using (stdGaussian_norm_secondMoment (E := ℂ))
  exact normalizedEmpiricalLaw_strongLaw iidComplexGaussian
    (fun i z => z i) (fun i => measurable_pi_apply i) hmem
    (fun i j hij => iidComplexGaussian_independent.indepFun hij)
    iidComplexGaussian_identDistrib ⟨stdGaussian ℂ, inferInstance⟩
    (iidComplexGaussian_coordinate 0).map_eq 2 (by norm_num) hmean

end OperatorPhaseRetrieval

end
