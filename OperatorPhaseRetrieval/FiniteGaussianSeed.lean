module

public import OperatorPhaseRetrieval.FiniteHaarModels
public import OperatorPhaseRetrieval.GaussianProducts

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory NormedSpace
open scoped ENNReal

namespace OperatorPhaseRetrieval

variable (ι : Type*) [Fintype ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

local instance finiteGaussianSeed_realInner : InnerProductSpace ℝ (EuclideanSpace ℂ ι) :=
  InnerProductSpace.rclikeToReal ℂ _

omit [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
theorem finiteGaussianSeed_measurable : Measurable (finiteGaussianSeed ι) := by
  have hn : Measurable (NormedSpace.normalize : EuclideanSpace ℂ ι → EuclideanSpace ℂ ι) :=
    measurable_norm.inv.smul measurable_id
  apply measurable_pi_iff.mpr
  intro i
  exact (((PiLp.continuous_apply 2 (fun _ : ι => ℂ) i).const_smul
    (Real.sqrt (Fintype.card ι))).measurable.comp hn)

/-- The seed representation uses independent Gaussian coordinates, not only a
rotation-invariant multivariate distribution. -/
theorem finiteHaarSeed_iid_gaussian_law :
    (haarSixProbability ι : Measure _).map (finiteHaarSeed ι) =
      (Measure.pi (fun _ : ι => stdGaussian ℂ)).map
        (fun z : ι → ℂ => finiteGaussianSeed ι (WithLp.toLp 2 z)) := by
  rw [finiteHaarSeed_gaussian_law, ← stdGaussian_complex_pi_law (ι := ι)]
  rw [Measure.map_map (finiteGaussianSeed_measurable ι)
    (PiLp.continuous_toLp 2 (fun _ : ι => ℂ)).measurable]
  rfl

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
theorem finiteGaussianSeed_empirical_normalization (z : ι → ℂ) (i : ι) :
    finiteGaussianSeed ι (WithLp.toLp 2 z) i =
      (Real.sqrt ((Fintype.card ι : ℝ)⁻¹ * ∑ j, ‖z j‖ ^ 2))⁻¹ • z i := by
  have hs : Real.sqrt ((Fintype.card ι : ℝ)⁻¹ * ∑ j, ‖z j‖ ^ 2) =
      (Real.sqrt (Fintype.card ι))⁻¹ * ‖WithLp.toLp 2 z‖ := by
    rw [← PiLp.norm_sq_eq_of_L2 (fun _ : ι => ℂ) (WithLp.toLp 2 z),
      Real.sqrt_mul (by positivity), Real.sqrt_inv, Real.sqrt_sq (norm_nonneg _)]
  rw [hs]
  simp only [finiteGaussianSeed, NormedSpace.normalize, PiLp.smul_apply,
    smul_smul, mul_inv_rev, inv_inv]
  congr 1
  ring

end OperatorPhaseRetrieval

end
