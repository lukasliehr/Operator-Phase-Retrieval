module

public import OperatorPhaseRetrieval.GaussianSphere

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex WithLp
open scoped ENNReal

namespace OperatorPhaseRetrieval

variable {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The standard Gaussian on a finite Hilbert direct sum is the product of its
standard Gaussian coordinate laws. -/
theorem stdGaussian_pi_law :
    (Measure.pi (fun _ : ι => stdGaussian E)).map (WithLp.toLp 2) =
      stdGaussian (PiLp 2 (fun _ : ι => E)) := by
  apply Measure.ext_of_charFun (E := PiLp 2 (fun _ : ι => E))
  ext t
  rw [charFun_pi, charFun_stdGaussian]
  simp_rw [charFun_stdGaussian]
  rw [← Complex.exp_sum]
  simp_rw [← Complex.ofReal_pow]
  rw [PiLp.norm_sq_eq_of_L2]
  simp [Finset.sum_div, neg_div]

section Complex

local instance gaussianProducts_realInner : InnerProductSpace ℝ (EuclideanSpace ℂ ι) :=
  InnerProductSpace.rclikeToReal ℂ _

/-- Product law with the real structure obtained by restricting complex scalars. -/
theorem stdGaussian_complex_pi_law :
    (Measure.pi (fun _ : ι => stdGaussian ℂ)).map (WithLp.toLp 2) =
      stdGaussian (EuclideanSpace ℂ ι) := by
  have hi (x y : EuclideanSpace ℂ ι) :
      inner ℝ x y = ∑ i, inner ℝ (x i) (y i) := by
    change (inner ℂ x y).re = _
    rw [PiLp.inner_apply, Complex.re_sum]
    rfl
  have hc (t : EuclideanSpace ℂ ι) :
      charFun ((Measure.pi (fun _ : ι => stdGaussian ℂ)).map (WithLp.toLp 2)) t =
        ∏ i, charFun (stdGaussian ℂ) (t i) := by
    simp_rw [charFun, hi, ← MeasurableEquiv.coe_toLp, ← integral_fintype_prod_eq_prod,
      integral_map_equiv]
    simp [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  apply Measure.ext_of_charFun (E := EuclideanSpace ℂ ι)
  ext t
  rw [hc, charFun_stdGaussian]
  simp_rw [charFun_stdGaussian]
  rw [← Complex.exp_sum]
  simp_rw [← Complex.ofReal_pow]
  rw [PiLp.norm_sq_eq_of_L2]
  simp [Finset.sum_div, neg_div]

end Complex

end OperatorPhaseRetrieval

end
