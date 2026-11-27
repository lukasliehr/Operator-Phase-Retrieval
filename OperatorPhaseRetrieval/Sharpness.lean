import OperatorPhaseRetrieval.TwoMeasurements
import OperatorPhaseRetrieval.DiagonalComplement
import OperatorPhaseRetrieval.AmplificationTheorem

/-! # Sharpness of the single-projection family of Theorem C -/

noncomputable section

open MeasureTheory

namespace OperatorPhaseRetrieval

def scalarOperator (c : ℝ) : ℂ →L[ℂ] ℂ := (c : ℂ) • 1

theorem scalarOperator_selfAdjoint (c : ℝ) : IsSelfAdjoint (scalarOperator c) :=
  (show IsSelfAdjoint (c : ℂ) from by simp [IsSelfAdjoint]).smul (IsSelfAdjoint.one _)

theorem scalarOperator_commute (c d : ℝ) : Commute (scalarOperator c) (scalarOperator d) := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [scalarOperator, mul_apply_eq_comp, smul_apply, one_apply_eq_self, smul_eq_mul]
  ring

theorem scalarOperator_sq (c d : ℝ) (h : c ^ 2 + d ^ 2 = 1) :
    scalarOperator c * scalarOperator c + scalarOperator d * scalarOperator d = 1 := by
  apply ContinuousLinearMap.ext
  intro z
  have hc : (c : ℂ) ^ 2 + (d : ℂ) ^ 2 = 1 := by exact_mod_cast h
  simp only [scalarOperator, add_apply, mul_apply_eq_comp, smul_apply, one_apply_eq_self,
    smul_eq_mul]
  linear_combination z * hc

def scalarMeasurement (c d : ℝ) (h : c ^ 2 + d ^ 2 = 1) (η : ℂ) (hη : IsPhase η) :
    SumL2 ℂ ≃ₗᵢ[ℂ] SumL2 ℂ := by
  let U : unitary (SumL2 ℂ →L[ℂ] SumL2 ℂ) :=
    ⟨phaseFamily (secondProjection (H := ℂ)) η,
      phaseFamily_unitary _ second_isProjection hη⟩
  let V : unitary (SumL2 ℂ →L[ℂ] SumL2 ℂ) :=
    ⟨blockRotation (scalarOperator c) (scalarOperator d),
      block_unitary _ _ (scalarOperator_selfAdjoint c) (scalarOperator_selfAdjoint d)
        (scalarOperator_commute c d) (scalarOperator_sq c d h)⟩
  exact (Unitary.linearIsometryEquiv U).trans (Unitary.linearIsometryEquiv V)

theorem scalarMeasurement_fst (c d : ℝ) (h : c ^ 2 + d ^ 2 = 1)
    (η : ℂ) (hη : IsPhase η) (x : SumL2 ℂ) :
    (scalarMeasurement c d h η hη x).fst = (c : ℂ) * x.fst - η * ((d : ℂ) * x.snd) := by
  change (blockRotation (scalarOperator c) (scalarOperator d)
    (phaseFamily secondProjection η x)).fst = _
  simp only [block_fst, scalarOperator, phaseFamily, add_apply, smul_apply, one_apply_eq_self,
    WithLp.add_fst, WithLp.add_snd, WithLp.smul_fst, WithLp.smul_snd,
    second_fst, second_snd, smul_eq_mul]
  ring

theorem scalarMeasurement_snd (c d : ℝ) (h : c ^ 2 + d ^ 2 = 1)
    (η : ℂ) (hη : IsPhase η) (x : SumL2 ℂ) :
    (scalarMeasurement c d h η hη x).snd = (d : ℂ) * x.fst + η * ((c : ℂ) * x.snd) := by
  change (blockRotation (scalarOperator c) (scalarOperator d)
    (phaseFamily secondProjection η x)).snd = _
  simp only [block_snd, scalarOperator, phaseFamily, add_apply, smul_apply, one_apply_eq_self,
    WithLp.add_fst, WithLp.add_snd, WithLp.smul_fst, WithLp.smul_snd,
    second_fst, second_snd, smul_eq_mul]
  ring

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def liftCoordinates (u : L2 μ) (x : SumL2 ℂ) : SumL2 (L2 μ) :=
  pairL2 (x.fst • u) (x.snd • u)

theorem liftCoordinates_smul (u : L2 μ) (ω : ℂ) (x : SumL2 ℂ) :
    liftCoordinates u (ω • x) = ω • liftCoordinates u x := by
  apply sum_ext <;> simp [liftCoordinates, WithLp.smul_fst, WithLp.smul_snd, smul_smul]

theorem liftCoordinates_injective (u : L2 μ) (hu : u ≠ 0) :
    Function.Injective (liftCoordinates u) := by
  intro x y he
  have hf := congrArg (fun z : SumL2 (L2 μ) => z.fst) he
  have hs := congrArg (fun z : SumL2 (L2 μ) => z.snd) he
  change x.fst • u = y.fst • u at hf
  change x.snd • u = y.snd • u at hs
  apply sum_ext
  · apply sub_eq_zero.mp
    exact (smul_eq_zero.mp (show (x.fst - y.fst) • u = 0 by rw [sub_smul, hf, sub_self])).resolve_right hu
  · apply sub_eq_zero.mp
    exact (smul_eq_zero.mp (show (x.snd - y.snd) • u = 0 by rw [sub_smul, hs, sub_self])).resolve_right hu

theorem modEq_smul_of_norm_eq (u : L2 μ) {a b : ℂ} (h : ‖a‖ = ‖b‖) :
    ModEq (a • u) (b • u) := by
  filter_upwards [Lp.coeFn_smul a u, Lp.coeFn_smul b u] with t ha hb
  rw [ha, hb]
  simp only [Pi.smul_apply, norm_smul, h]

theorem liftCoordinates_modEq (u : L2 μ) {x y : SumL2 ℂ} (h : CoordinateModEq x y) :
    PairModEq (liftCoordinates u x) (liftCoordinates u y) :=
  ⟨modEq_smul_of_norm_eq u h.1, modEq_smul_of_norm_eq u h.2⟩

theorem block_measurement_lift (C D : L2 μ →L[ℂ] L2 μ)
    (hC : IsSelfAdjoint C) (hD : IsSelfAdjoint D) (hc : Commute C D)
    (hsq : C * C + D * D = 1) (u : L2 μ) (c d : ℝ)
    (hCu : C u = (c : ℂ) • u) (hDu : D u = (d : ℂ) • u)
    (hcd : c ^ 2 + d ^ 2 = 1) (η : ℂ) (hη : IsPhase η) (x : SumL2 ℂ) :
    phaseFamily (blockProjection C D) η (blockRotation C D (liftCoordinates u x)) =
      liftCoordinates u (scalarMeasurement c d hcd η hη x) := by
  rw [block_measurement C D hC hD hc hsq]
  apply sum_ext <;>
    simp only [liftCoordinates, pairL2_fst, pairL2_snd, map_smul, hCu, hDu,
      scalarMeasurement_fst, scalarMeasurement_snd] <;> module

/-- Any common eigenvector supplies a two-dimensional obstruction for every pair of phases. -/
theorem block_two_phases_not_phase_retrieval (C D : L2 μ →L[ℂ] L2 μ)
    (hC : IsSelfAdjoint C) (hD : IsSelfAdjoint D) (hc : Commute C D)
    (hsq : C * C + D * D = 1) (u : L2 μ) (hu : u ≠ 0) (c d : ℝ)
    (hCu : C u = (c : ℂ) • u) (hDu : D u = (d : ℂ) • u)
    (hcd : c ^ 2 + d ^ 2 = 1) (η ξ : ℂ) (hη : IsPhase η) (hξ : IsPhase ξ) :
    ∃ x y : SumL2 (L2 μ),
      PairModEq (phaseFamily (blockProjection C D) η x) (phaseFamily (blockProjection C D) η y) ∧
      PairModEq (phaseFamily (blockProjection C D) ξ x) (phaseFamily (blockProjection C D) ξ y) ∧
      ¬ PhaseRelated x y := by
  obtain ⟨x, y, h₁, h₂, hn⟩ := two_unitaries_not_phase_retrieval
    (scalarMeasurement c d hcd η hη) (scalarMeasurement c d hcd ξ hξ)
  let V := blockRotation C D
  have hV := block_unitary C D hC hD hc hsq
  refine ⟨V (liftCoordinates u x), V (liftCoordinates u y), ?_, ?_, ?_⟩
  · rw [block_measurement_lift C D hC hD hc hsq u c d hCu hDu hcd η hη,
      block_measurement_lift C D hC hD hc hsq u c d hCu hDu hcd η hη]
    exact liftCoordinates_modEq u h₁
  · rw [block_measurement_lift C D hC hD hc hsq u c d hCu hDu hcd ξ hξ,
      block_measurement_lift C D hC hD hc hsq u c d hCu hDu hcd ξ hξ]
    exact liftCoordinates_modEq u h₂
  · rintro ⟨ω, hω, he⟩
    apply hn
    refine ⟨ω, hω, liftCoordinates_injective u hu ?_⟩
    apply (Unitary.linearIsometryEquiv ⟨V, hV⟩).injective
    change V (liftCoordinates u y) = V (liftCoordinates u (ω • x))
    rw [liftCoordinates_smul, V.map_smul]
    exact he

end OperatorPhaseRetrieval

end
