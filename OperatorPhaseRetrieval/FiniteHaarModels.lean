import OperatorPhaseRetrieval.FiniteProbabilityL2
import OperatorPhaseRetrieval.GaussianSphere
import OperatorPhaseRetrieval.ExpressionModels

/-! The six independent Haar matrices as actual normalized finite L² models. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric NormedSpace
open scoped ENNReal

namespace OperatorPhaseRetrieval

variable (ι : Type*) [Fintype ι]

def haarSixProbability : ProbabilityMeasure (Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) :=
  ⟨Measure.pi (fun _ : Fin 6 => (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure (HaarUnitary (EuclideanSpace ℂ ι)))),
    inferInstance⟩

theorem haarSix_tail_measurePreserving :
    MeasurePreserving (fun U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι) => fun j : Fin 5 => U j.succ)
      (haarSixProbability ι : Measure _) (haarFiveProbability ι : Measure (Fin 5 → HaarUnitary (EuclideanSpace ℂ ι))) := by
  have h := measurePreserving_piFinSuccAbove
    (fun _ : Fin 6 => (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure (HaarUnitary (EuclideanSpace ℂ ι)))) 0
  have h' := (measurePreserving_snd
    (μ := (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure (HaarUnitary (EuclideanSpace ℂ ι))))
    (ν := (haarFiveProbability ι : Measure (Fin 5 → HaarUnitary (EuclideanSpace ℂ ι))))).comp h
  convert h' using 1
  · funext U j
    exact congrArg U (congrFun Fin.succAbove_zero j).symm
  · rfl

theorem haarSix_coordinate_measurePreserving (j : Fin 6) :
    MeasurePreserving (fun U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι) => U j)
      (haarSixProbability ι : Measure _) (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure (HaarUnitary (EuclideanSpace ℂ ι))) :=
  measurePreserving_eval (fun _ : Fin 6 => (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure (HaarUnitary (EuclideanSpace ℂ ι)))) j

variable [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

def finiteHaarModel (U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) :
    Fin 6 → L2 (finiteProbability ι) ≃ₗᵢ[ℂ] L2 (finiteProbability ι) :=
  fun j => finiteL2Unitary ι (U j)

theorem finiteHaarModel_stability_failure_le (hn : 50 ≤ Fintype.card ι) :
    (haarSixProbability ι : Measure _)
      {U | ¬ StableUnitaryFamily stabilityConstant (fun j : Fin 5 => finiteHaarModel ι U j.succ)} ≤
      ENNReal.ofReal ((2 : ℝ) ^ (1485 - 32 * (Fintype.card ι : ℤ))) := by
  have hm : MeasurableSet {U : Fin 5 → HaarUnitary (EuclideanSpace ℂ ι) |
      ¬ StableUnitaryFamily stabilityConstant (fun j => finiteL2Unitary ι (U j))} := by
    simp_rw [finiteL2Unitary_stable_iff]
    exact (coordinateStableFamily_measurableSet _).compl
  have he := (haarSix_tail_measurePreserving ι).measure_preimage hm.nullMeasurableSet
  exact he.trans_le (finiteL2_haar_stability_failure_le ι hn)

theorem finiteHaarModel_stability_failure_quarter (hn : 50 ≤ Fintype.card ι) :
    (haarSixProbability ι : Measure _)
      {U | ¬ StableUnitaryFamily stabilityConstant (fun j : Fin 5 => finiteHaarModel ι U j.succ)} ≤
      1 / 4 := by
  apply (finiteHaarModel_stability_failure_le ι hn).trans
  have h : (2 : ℝ) ^ (1485 - 32 * (Fintype.card ι : ℤ)) ≤ 1 / 4 := by
    calc
      _ ≤ (2 : ℝ) ^ (-2 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ = _ := by norm_num
  simpa using ENNReal.ofReal_le_ofReal h

/-- The actual coordinate values of the auxiliary seed `U₀ 1`. -/
def finiteHaarSeed (U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι)) : ι → ℂ :=
  fun i => (finiteHaarModel ι U 0 (Lp.const 2 (finiteProbability ι) 1)) i

/-- A Gaussian direction scaled to normalized counting L² norm one. -/
def finiteGaussianSeed (g : EuclideanSpace ℂ ι) : ι → ℂ :=
  fun i => Real.sqrt (Fintype.card ι) • (NormedSpace.normalize g) i

local instance finiteHaarModels_realInner : InnerProductSpace ℝ (EuclideanSpace ℂ ι) :=
  InnerProductSpace.rclikeToReal ℂ _

/-- The representation in the proof of Lemma 4.9, as equality of laws of the
whole seed vector. The zero Gaussian vector is a null event. -/
theorem finiteHaarSeed_gaussian_law :
    (haarSixProbability ι : Measure _).map (finiteHaarSeed ι) =
      (stdGaussian (EuclideanSpace ℂ ι)).map (finiteGaussianSeed ι) := by
  let f : EuclideanSpace ℂ ι := (finiteL2Equiv ι ℂ).symm (Lp.const 2 (finiteProbability ι) 1)
  have hf : ‖f‖ = 1 := by simp [f, Lp.norm_const]
  let scale : EuclideanSpace ℂ ι → (ι → ℂ) := fun z i => Real.sqrt (Fintype.card ι) • z i
  have hm : Measurable scale := by
    apply measurable_pi_lambda
    intro i
    change Measurable (fun z : EuclideanSpace ℂ ι => (Real.sqrt (Fintype.card ι) : ℝ) • z i)
    exact ((PiLp.continuous_apply 2 (fun _ : ι => ℂ) i).const_smul (Real.sqrt (Fintype.card ι))).measurable
  have he : finiteHaarSeed ι = fun U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι) =>
      scale ((U 0 : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) f) := by
    funext U i
    have h := finiteL2Unitary_apply ι (U 0) f
    rw [(finiteL2Equiv ι ℂ).apply_symm_apply] at h
    change finiteL2Unitary ι (U 0) (Lp.const 2 (finiteProbability ι) 1) i = _
    rw [h, finiteL2Equiv_apply]
  have hu : Measurable (fun U : HaarUnitary (EuclideanSpace ℂ ι) =>
      (U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) f) :=
    (continuous_subtype_val.clm_apply continuous_const).measurable
  rw [he]
  calc
    _ = (((haarSixProbability ι : Measure _).map
        (fun U : Fin 6 → HaarUnitary (EuclideanSpace ℂ ι) => U 0)).map
        (fun U : HaarUnitary (EuclideanSpace ℂ ι) => (U : _ →L[ℂ] _) f)).map scale := by
      rw [Measure.map_map hu (measurable_pi_apply 0),
        Measure.map_map hm (hu.comp (measurable_pi_apply 0))]
      rfl
    _ = ((stdGaussian (EuclideanSpace ℂ ι)).map NormedSpace.normalize).map scale := by
      rw [(haarSix_coordinate_measurePreserving ι 0).map_eq,
        haarUnitary_unitVector_gaussian_law _ f hf]
    _ = _ := by
      have hnorm : Measurable (NormedSpace.normalize : EuclideanSpace ℂ ι → EuclideanSpace ℂ ι) :=
        measurable_norm.inv.smul measurable_id
      rw [Measure.map_map hm hnorm]
      rfl

end OperatorPhaseRetrieval

end
