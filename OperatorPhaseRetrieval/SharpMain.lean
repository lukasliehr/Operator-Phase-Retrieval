module

public import OperatorPhaseRetrieval.Sharpness
public import OperatorPhaseRetrieval.TransferredInstability

@[expose] public section

/-! # Theorem C with sharpness and instability for the same projection

This strengthens Theorem C on `L²(ℝ)` by a sharpness and an instability statement.
-/

noncomputable section

open MeasureTheory

namespace OperatorPhaseRetrieval

/-- Theorem C with sharpness and instability, all for a single projection. -/
theorem main_with_sharpness_and_full_instability :
    ∃ P : RealL2 →L[ℂ] RealL2, IsOrthogonalProjection P ∧
      (∀ η : Fin 3 → ℂ, (∀ j, IsPhase (η j)) → Function.Injective η →
        (∀ j, IsUnitary (phaseFamily P (η j))) ∧
        ∀ f g, (∀ j, ModEq (phaseFamily P (η j) f) (phaseFamily P (η j) g)) →
          PhaseRelated f g) ∧
      (∀ η ξ : ℂ, IsPhase η → IsPhase ξ →
        ∃ f g, ModEq (phaseFamily P η f) (phaseFamily P η g) ∧
          ModEq (phaseFamily P ξ f) (phaseFamily P ξ g) ∧ ¬ PhaseRelated f g) ∧
      ¬ L2UniformPhaseRecovery (fun η : {η : ℂ // IsPhase η} => phaseFamily P η.1) := by
  obtain ⟨μ, hfin, hμ0, hμv, hm, hd⟩ := exists_polynomial_dense_measure
  let : IsFiniteMeasure μ := hfin
  let : NeZero μ := ⟨hμ0⟩
  let : NullSingletonClass μ := ⟨fun z => hμv (measure_singleton z)⟩
  obtain ⟨b, p, hp⟩ := polynomial_hilbertBasis_of_dense hμv hm hd
  let w := smoothingWeight p
  let C := diagonalSmoothing b w
  let D := diagonalComplement b w
  have hw : Summable w := smoothingWeight_summable p
  have hb : ∀ n, |w n| ≤ 1 := by
    intro n
    rw [abs_of_pos (smoothingWeight_pos p n)]
    have hl := smoothingWeight_le p n
    have hpow : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  have hC : IsSelfAdjoint C := diagonalSmoothing_selfAdjoint b hw
  have hD : IsSelfAdjoint D := diagonalComplement_selfAdjoint b hw hb
  have hc : Commute C D := diagonalComplement_commute b hw hb
  have hsq : C * C + D * D = 1 := diagonalComplement_sq b hw hb
  have hn : ‖C‖ ≤ (1 : ℝ) / 8 :=
    (diagonalSmoothing_norm_le b hw (fun n => (smoothingWeight_pos p n).le)).trans
      (smoothingWeight_tsum_le p)
  have hs : ‖C‖ ^ 2 < (1 : ℝ) / 2 := by nlinarith [norm_nonneg C]
  have hr := polynomialSmoothing_rigid hμv b p hp
  have hP := amplification_with_complement C D hC hD hc hsq hs hr
  obtain ⟨W, hW⟩ := exists_double_spatial_unitary μ (volume : Measure ℝ)
  let P := blockProjection C D
  let Q := transport W P
  have hQ : IsOrthogonalProjection Q := transport_projection W hP.1
  refine ⟨Q, hQ, ?_, ?_, ?_⟩
  · intro η hη hi
    refine ⟨fun j => phaseFamily_unitary Q hQ (hη j), ?_⟩
    intro f g hm
    have hdata : ∀ j, PairModEq (phaseFamily P (η j) (W f)) (phaseFamily P (η j) (W g)) := by
      intro j
      have he := (hW _ _).mpr (hm j)
      simpa only [Q, map_phaseFamily_transport] using he
    obtain ⟨ω, hω, he⟩ := (hP.2 η hη hi).2 (W f) (W g) hdata
    exact ⟨ω, hω, W.injective (by simpa only [W.map_smul] using he)⟩
  · intro η ξ hη hξ
    have hu : b 0 ≠ 0 := by
      intro hz
      have he := b.orthonormal.norm_eq_one 0
      rw [hz, norm_zero] at he
      norm_num at he
    have hb0 : w 0 ^ 2 ≤ 1 := by nlinarith [hb 0, sq_abs (w 0), abs_nonneg (w 0)]
    have hcd : w 0 ^ 2 + Real.sqrt (1 - w 0 ^ 2) ^ 2 = 1 := by
      rw [Real.sq_sqrt (by linarith)]
      ring
    obtain ⟨x, y, h₁, h₂, hne⟩ := block_two_phases_not_phase_retrieval C D hC hD hc hsq
      (b 0) hu (w 0) (Real.sqrt (1 - w 0 ^ 2))
      (diagonalSmoothing_basis b hw 0) (diagonalComplement_basis b hw hb 0) hcd η ξ hη hξ
    refine ⟨W.symm x, W.symm y, ?_, ?_, ?_⟩
    · apply (hW _ _).mp
      simpa only [Q, map_phaseFamily_transport, W.apply_symm_apply] using h₁
    · apply (hW _ _).mp
      simpa only [Q, map_phaseFamily_transport, W.apply_symm_apply] using h₂
    · rintro ⟨ω, hω, he⟩
      exact hne ⟨ω, hω, by simpa only [W.map_smul, W.apply_symm_apply] using congrArg W he⟩
  · exact transported_no_uniform_recovery W hW D b hw hD hc hsq
      (fun η : {η : ℂ // IsPhase η} => η.1) (fun η => η.2)

/-- Theorem C and instability for one and the same projection. -/
theorem main_with_instability :
    ∃ P : RealL2 →L[ℂ] RealL2, IsOrthogonalProjection P ∧
      ∀ η : Fin 3 → ℂ, (∀ j, IsPhase (η j)) → Function.Injective η →
        (∀ j, IsUnitary (phaseFamily P (η j))) ∧
        (∀ f g, (∀ j, ModEq (phaseFamily P (η j) f) (phaseFamily P (η j) g)) →
          PhaseRelated f g) ∧
        ¬ L2UniformPhaseRecovery (fun j => phaseFamily P (η j)) := by
  obtain ⟨P, hP, hretr, _, hfull⟩ := main_with_sharpness_and_full_instability
  refine ⟨P, hP, fun η hη hi => ⟨(hretr η hη hi).1, (hretr η hη hi).2, ?_⟩⟩
  intro hstable
  apply hfull
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hstable ε hε
  exact ⟨δ, hδ, fun f g hf hg hm => h f g hf hg (fun j => hm ⟨η j, hη j⟩)⟩

end OperatorPhaseRetrieval

end
