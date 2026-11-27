import OperatorPhaseRetrieval.TwoUnitaryFourier
import OperatorPhaseRetrieval.SpatialExistence
import OperatorPhaseRetrieval.SpatialTransfer
import OperatorPhaseRetrieval.Formulations

/-! Transfer of the two measurements from normalized circle measure to the real line. -/
noncomputable section

open MeasureTheory
namespace OperatorPhaseRetrieval.TwoUnitary

private theorem nullSingleton_haar : NullSingletonClass μ := by
  constructor
  intro x
  have hh : (volume : Measure UnitAddCircle) = μ := by
    simpa using AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ))
  rw [← hh, ← Metric.closedBall_zero, AddCircle.volume_closedBall]
  norm_num

theorem transfer_to_line (ε : ℝ) (V : Op) (hV : IsUnitary V) (hne : ‖V - 1‖ < ε)
    (hpr : ∀ f g : H, ModEq f g → ModEq (V f) (V g) → ∃ c : Circle, g = c • f) :
    ∃ U : L2 (volume : Measure ℝ) →L[ℂ] L2 (volume : Measure ℝ),
      (Isometry U ∧ Function.Surjective U) ∧ ‖U - 1‖ < ε ∧
      ∀ f g, ModEq f g → ModEq (U f) (U g) → ∃ c : Circle, g = c • f := by
  let : NullSingletonClass μ := nullSingleton_haar
  obtain ⟨W,hW⟩ := exists_spatial_unitary (volume : Measure ℝ) μ
  let U := transport W V
  have hnorm (x : L2 (volume : Measure ℝ)) : ‖(U - 1) x‖ = ‖(V - 1) (W x)‖ := by
    rw [← W.norm_map ((U - 1) x)]
    simp [U, map_sub, sub_apply, transport_apply]
  refine ⟨U,⟨W.symm.isometry.comp (hV.isometry_surjective.1.comp W.isometry),
    W.symm.surjective.comp (hV.isometry_surjective.2.comp W.surjective)⟩, ?_, ?_⟩
  · apply lt_of_le_of_lt _ hne
    refine (U - 1).opNorm_le_bound (norm_nonneg _) (fun x => ?_)
    rw [hnorm, ← W.norm_map x]
    exact (V - 1).le_opNorm _
  · intro f g hfg hU
    have hm := (hW (U f) (U g)).2 hU
    change ModEq (W (transport W V f)) (W (transport W V g)) at hm
    simp only [map_transport] at hm
    obtain ⟨c,hc⟩ := hpr (W f) (W g) ((hW f g).2 hfg) hm
    refine ⟨c,W.injective ?_⟩
    change W g = W ((c : ℂ) • f)
    rwa [W.map_smul]

/-- A single surjective measurement, in particular any unitary, cannot determine the phase.
The zeroth and first Fourier modes have equal magnitude and are orthogonal. -/
theorem one_measurement_fails (A : L2 (volume : Measure ℝ) →L[ℂ] L2 (volume : Measure ℝ))
    (hA : Function.Surjective A) : ∃ f g, ModEq (A f) (A g) ∧ ¬ ∃ c : Circle, g = c • f := by
  let : NullSingletonClass μ := nullSingleton_haar
  obtain ⟨W,hW⟩ := exists_spatial_unitary (volume : Measure ℝ) μ
  obtain ⟨f,hf⟩ := (W.surjective.comp hA) (basis 0)
  obtain ⟨g,hg⟩ := (W.surjective.comp hA) (basis 1)
  change W (A f) = basis 0 at hf
  change W (A g) = basis 1 at hg
  refine ⟨f,g,(hW _ _).mp ?_, ?_⟩
  · rw [hf,hg]
    unfold ModEq
    rw [coe_fourierBasis]
    filter_upwards [coeFn_fourierLp (T := 1) 2 0, coeFn_fourierLp (T := 1) 2 1]
      with x hx₀ hx₁
    rw [hx₀,hx₁]
    exact (Circle.norm_coe _).trans (Circle.norm_coe _).symm
  · rintro ⟨c,hc⟩
    change g = (c : ℂ) • f at hc
    rw [hc, A.map_smul, W.map_smul, hf] at hg
    have h := congrArg (inner ℂ (basis 1)) hg
    simp only [inner_smul_right, orthonormal_iff_ite.mp basis.orthonormal] at h
    norm_num at h

end OperatorPhaseRetrieval.TwoUnitary
