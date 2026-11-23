import OperatorPhaseRetrieval.CoordinateDensity

/-! Joint coordinate laws obtained by evaluating the actual countable syntax. -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal Topology InnerProductSpace

namespace OperatorPhaseRetrieval

namespace StabilityExpression

local instance : Encodable StabilityExpression := Encodable.ofCountable _

def index (t : StabilityExpression) : ℕ := Encodable.encode t

def ofIndex (n : ℕ) : StabilityExpression := (Encodable.decode n).getD .one

@[simp]
theorem ofIndex_index (t : StabilityExpression) : ofIndex t.index = t := by
  simp [ofIndex, index, Encodable.encodek]

def coordinateOperations : CoordinateOperations where
  one := index .one
  add r s := index (.add (ofIndex r) (ofIndex s))
  smul a b r := index (.smul a b (ofIndex r))
  conj r := index (.conj (ofIndex r))
  modulus r := index (.modulus (ofIndex r))

def forwardIndex (j : Fin 5) (r : ℕ) : ℕ := index (.apply j false (ofIndex r))

def inverseIndex (j : Fin 5) (r : ℕ) : ℕ := index (.apply j true (ofIndex r))

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (U : Fin 6 → L2 μ ≃ₗᵢ[ℂ] L2 μ)

/-- All formal expressions evaluated at one point of the original probability space. -/
def coordinateMap (x : X) (r : ℕ) : ℂ := eval U (ofIndex r) x

theorem coordinateMap_measurable : Measurable (coordinateMap μ U) :=
  measurable_pi_lambda _ (fun r => (Lp.stronglyMeasurable (eval U (ofIndex r))).measurable)

/-- The actual joint law of the evaluated formal expressions. -/
def jointLaw : ProbabilityMeasure (ℕ → ℂ) :=
  ⟨μ.map (coordinateMap μ U), Measure.isProbabilityMeasure_map (coordinateMap_measurable μ U).aemeasurable⟩

theorem jointLaw_memLp (r : ℕ) :
    MemLp (fun z : ℕ → ℂ => z r) 2 (jointLaw μ U : Measure (ℕ → ℂ)) := by
  apply (memLp_map_measure_iff (measurable_pi_apply r).aestronglyMeasurable
    (coordinateMap_measurable μ U).aemeasurable).mpr
  exact Lp.memLp (eval U (ofIndex r))

theorem jointLaw_algebraLaws :
    CoordinateAlgebraLaws coordinateOperations (jointLaw μ U : Measure (ℕ → ℂ)) where
  one := by
    apply (ae_map_iff (coordinateMap_measurable μ U).aemeasurable
      ((isClosed_eq (continuous_apply coordinateOperations.one) continuous_const).measurableSet)).mpr
    simpa only [Filter.EventuallyEq, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Function.const_apply, Function.comp_apply, coordinateMap, coordinateOperations, ofIndex_index, eval] using
      Lp.coeFn_const 2 μ (1 : ℂ)
  add r s := by
    apply (ae_map_iff (coordinateMap_measurable μ U).aemeasurable
      ((isClosed_eq (continuous_apply (coordinateOperations.add r s))
        ((continuous_apply r).add (continuous_apply s))).measurableSet)).mpr
    simpa only [Filter.EventuallyEq, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Function.const_apply, Function.comp_apply, coordinateMap, coordinateOperations, ofIndex_index, eval] using
      Lp.coeFn_add (eval U (ofIndex r)) (eval U (ofIndex s))
  smul a b r := by
    apply (ae_map_iff (coordinateMap_measurable μ U).aemeasurable
      ((isClosed_eq (continuous_apply (coordinateOperations.smul a b r))
        (continuous_const.mul (continuous_apply r))).measurableSet)).mpr
    simpa only [Filter.EventuallyEq, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Function.const_apply, Function.comp_apply, coordinateMap, coordinateOperations, ofIndex_index, eval, smul_eq_mul] using
      Lp.coeFn_smul (rationalComplex a b) (eval U (ofIndex r))
  conj r := by
    apply (ae_map_iff (coordinateMap_measurable μ U).aemeasurable
      ((isClosed_eq (continuous_apply (coordinateOperations.conj r))
        (continuous_apply r).star).measurableSet)).mpr
    simpa only [Filter.EventuallyEq, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Function.const_apply, Function.comp_apply, coordinateMap, coordinateOperations, ofIndex_index, eval] using
      conjugateL2_coeFn (eval U (ofIndex r))
  modulus r := by
    apply (ae_map_iff (coordinateMap_measurable μ U).aemeasurable
      ((isClosed_eq (continuous_apply (coordinateOperations.modulus r))
        (Complex.continuous_ofReal.comp (continuous_apply r).norm)).measurableSet)).mpr
    simpa only [Filter.EventuallyEq, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Function.const_apply, Function.comp_apply, coordinateMap, coordinateOperations, ofIndex_index, eval] using
      complexModulusL2_coeFn (eval U (ofIndex r))

theorem jointLaw_inverse (j : Fin 5) (r : ℕ) :
    ∀ᵐ z ∂(jointLaw μ U : Measure (ℕ → ℂ)), z (forwardIndex j (inverseIndex j r)) = z r := by
  apply (ae_map_iff (coordinateMap_measurable μ U).aemeasurable
    ((isClosed_eq (continuous_apply (forwardIndex j (inverseIndex j r)))
      (continuous_apply r)).measurableSet)).mpr
  exact Filter.Eventually.of_forall fun x => by
    simp [coordinateMap, forwardIndex, inverseIndex, eval, unitaryAction]

theorem jointLaw_fourthMoment (r : ℕ) :
    ∫⁻ z, ENNReal.ofReal (‖z r‖ ^ 4) ∂(jointLaw μ U : Measure (ℕ → ℂ)) =
      ∫⁻ x, ENNReal.ofReal (‖eval U (ofIndex r) x‖ ^ 4) ∂μ := by
  exact lintegral_map' (((continuous_apply r).norm.pow 4).measurable.ennreal_ofReal.aemeasurable) (coordinateMap_measurable μ U).aemeasurable

theorem coordinateMap_measurePreserving :
    MeasurePreserving (coordinateMap μ U) μ (jointLaw μ U : Measure (ℕ → ℂ)) :=
  ⟨coordinateMap_measurable μ U, rfl⟩

/-- Pullback identifies coordinate functions with the original evaluated expressions. -/
def jointLawPullback :
    L2 (jointLaw μ U : Measure (ℕ → ℂ)) →ₗᵢ[ℂ] L2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ (coordinateMap μ U) (coordinateMap_measurePreserving μ U)

theorem jointLawPullback_coordinate (r : ℕ) :
    jointLawPullback μ U (jointCoordinate (jointLaw μ U) (jointLaw_memLp μ U) r) =
      eval U (ofIndex r) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving
    (jointCoordinate (jointLaw μ U) (jointLaw_memLp μ U) r) (coordinateMap_measurePreserving μ U),
    ae_of_ae_map (coordinateMap_measurable μ U).aemeasurable
      (jointCoordinate_coeFn (jointLaw μ U) (jointLaw_memLp μ U) r)] with x hx hy
  exact hx.trans hy

theorem jointLaw_gram (j : Fin 5) (r s : ℕ) :
    ⟪jointCoordinate (jointLaw μ U) (jointLaw_memLp μ U) (forwardIndex j r),
      jointCoordinate (jointLaw μ U) (jointLaw_memLp μ U) (forwardIndex j s)⟫_ℂ =
      ⟪jointCoordinate (jointLaw μ U) (jointLaw_memLp μ U) r,
        jointCoordinate (jointLaw μ U) (jointLaw_memLp μ U) s⟫_ℂ := by
  rw [← (jointLawPullback μ U).inner_map_map, jointLawPullback_coordinate, jointLawPullback_coordinate]
  simp only [forwardIndex, ofIndex_index, eval, unitaryAction, Bool.false_eq_true, ↓reduceIte]
  rw [(U j.succ).inner_map_map]
  rw [← jointLawPullback_coordinate μ U r, ← jointLawPullback_coordinate μ U s,
    (jointLawPullback μ U).inner_map_map]

theorem jointLaw_phaseDistance (r s : ℕ) :
    phaseDistance (jointCoordinate (jointLaw μ U) (jointLaw_memLp μ U) r)
      (jointCoordinate (jointLaw μ U) (jointLaw_memLp μ U) s) =
      phaseDistance (eval U (ofIndex r)) (eval U (ofIndex s)) := by
  rw [← phaseDistance_map (jointLawPullback μ U), jointLawPullback_coordinate, jointLawPullback_coordinate]

def jointLawRealPullback :
    Lp ℝ 2 (jointLaw μ U : Measure (ℕ → ℂ)) →ₗᵢ[ℝ] Lp ℝ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℝ (coordinateMap μ U) (coordinateMap_measurePreserving μ U)

theorem jointLawRealPullback_magnitude (r : ℕ) :
    jointLawRealPullback μ U (magnitude (jointCoordinate (jointLaw μ U) (jointLaw_memLp μ U) r)) =
      magnitude (eval U (ofIndex r)) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving
    (magnitude (jointCoordinate (jointLaw μ U) (jointLaw_memLp μ U) r))
      (coordinateMap_measurePreserving μ U),
    ae_of_ae_map (coordinateMap_measurable μ U).aemeasurable
      (magnitude_coeFn (jointCoordinate (jointLaw μ U) (jointLaw_memLp μ U) r)),
    ae_of_ae_map (coordinateMap_measurable μ U).aemeasurable
      (jointCoordinate_coeFn (jointLaw μ U) (jointLaw_memLp μ U) r),
    magnitude_coeFn (eval U (ofIndex r))] with x hx hm hc he
  change Lp.compMeasurePreserving (coordinateMap μ U) (coordinateMap_measurePreserving μ U)
    (magnitude (jointCoordinate (jointLaw μ U) (jointLaw_memLp μ U) r)) x = _
  simp only [Function.comp_apply] at hx
  rw [hx, hm, hc, he]
  rfl

theorem jointLaw_magnitudeDistance (r s : ℕ) :
    ‖magnitude (jointCoordinate (jointLaw μ U) (jointLaw_memLp μ U) r) -
      magnitude (jointCoordinate (jointLaw μ U) (jointLaw_memLp μ U) s)‖ =
      ‖magnitude (eval U (ofIndex r)) - magnitude (eval U (ofIndex s))‖ := by
  rw [← (jointLawRealPullback μ U).norm_map, map_sub,
    jointLawRealPullback_magnitude, jointLawRealPullback_magnitude]

theorem jointLaw_measurementDistance (r s : ℕ) :
    coordinateMeasurementDistance (jointLaw μ U) (jointLaw_memLp μ U) forwardIndex r s =
      measurementDistance (fun j : Fin 5 => U j.succ) (eval U (ofIndex r)) (eval U (ofIndex s)) := by
  unfold coordinateMeasurementDistance measurementDistance
  calc
    _ = ‖fun j : Fin 5 => ‖magnitude (jointCoordinate (jointLaw μ U) (jointLaw_memLp μ U) (forwardIndex j r)) -
      magnitude (jointCoordinate (jointLaw μ U) (jointLaw_memLp μ U) (forwardIndex j s))‖‖ :=
        (norm_component_norms _).symm
    _ = ‖fun j : Fin 5 => ‖magnitude (U j.succ (eval U (ofIndex r))) -
      magnitude (U j.succ (eval U (ofIndex s)))‖‖ := by
        congr 1
        funext j
        rw [jointLaw_magnitudeDistance]
        simp only [forwardIndex, ofIndex_index, eval, unitaryAction, Bool.false_eq_true, ↓reduceIte]
    _ = _ := norm_component_norms _

/-- A stable family on the original space supplies the required coordinate-model
estimate; there is no additional stability assumption about the pushed-forward law. -/
theorem jointLaw_stable (hU : StableUnitaryFamily stabilityConstant (fun j : Fin 5 => U j.succ))
    (r s : ℕ) :
    stabilityConstant * phaseDistance (jointCoordinate (jointLaw μ U) (jointLaw_memLp μ U) r)
      (jointCoordinate (jointLaw μ U) (jointLaw_memLp μ U) s) ≤
      coordinateMeasurementDistance (jointLaw μ U) (jointLaw_memLp μ U) forwardIndex r s := by
  rw [jointLaw_phaseDistance, jointLaw_measurementDistance]
  exact hU _ _

end StabilityExpression

end OperatorPhaseRetrieval

end
