import OperatorPhaseRetrieval.TwoUnitaryFourier
import OperatorPhaseRetrieval.NearIdentity

/-! Small unitary rotations which extract a prescribed commutator. -/
noncomputable section

namespace OperatorPhaseRetrieval.TwoUnitary

/-- The orthogonal projection onto the negative eigenspace of a symmetry. -/
theorem symmetry_projection (R : Op) (hR : IsUnitary R) (hRs : star R = R) :
    IsOrthogonalProjection ((1 / 2 : ℂ) • (1 - R)) := by
  have hRR : R * R = 1 := by simpa only [hRs] using hR.1
  constructor
  · simp only [smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub,
      mul_one, one_mul, hRR]
    module
  · simp [star_sub, hRs]

/-- Rotate one eigenspace of a symmetry through an arbitrarily small phase. -/
theorem small_rotation (R : Op) (hR : IsUnitary R) (hRs : star R = R)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (W : Op) (z : ℂ), IsUnitary W ∧ z ≠ 0 ∧ W = 1 + z • (R-1) ∧ ‖W-1‖ < δ := by
  let t := δ / 4
  have ht : 0 < t := by dsimp [t]; positivity
  let η := cayley t
  let Q : Op := (1 / 2 : ℂ) • (1 - R)
  have hQ : IsOrthogonalProjection Q := symmetry_projection R hR hRs
  refine ⟨phaseFamily Q η, (1-η)/2, phaseFamily_unitary Q hQ (cayley_isPhase t), ?_, ?_, ?_⟩
  · exact div_ne_zero (sub_ne_zero.mpr (cayley_ne_one ht).symm) (by norm_num)
  · unfold phaseFamily Q
    rw [smul_smul]
    module
  · apply (projection_phase_norm_bound Q hQ η).trans_lt
    apply (cayley_norm_sub_one ht).trans_lt
    dsimp [t]
    linarith

/-- Earlier unitary factors commuting with the observable cancel from the readout. -/
theorem readout_rotation (V W R : Op) (N : ℤ) (z : ℂ)
    (hV : IsUnitary V) (hW : IsUnitary W) (hVN : Commute V (shift N))
    (hz : z ≠ 0) (h : W = 1 + z • (R-1)) :
    readout (V*W) N z = star W * (shift N * R - R * shift N) := by
  have hcancel : star V * shift N * V = shift N := by
    rw [mul_assoc, ← hVN.eq, ← mul_assoc, hV.1, one_mul]
  have hc : shift N * W - W * shift N = z • (shift N * R - R * shift N) := by
    rw [h]
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, one_mul, mul_one]
    module
  have he : star (V*W) * shift N * (V*W) - shift N = star W * (shift N * W - W * shift N) := by
    rw [star_mul, mul_sub]
    calc
      _ = star W * (star V * shift N * V) * W - shift N := by simp only [mul_assoc]
      _ = _ := by rw [hcancel, ← mul_assoc (star W) W, hW.1, one_mul, mul_assoc]
  rw [readout, he, hc, mul_smul_comm, inv_smul_smul₀ hz]

theorem exists_step (V R : Op) (N P : ℤ) (δ : ℝ) (hδ : 0 < δ) (hV : IsUnitary V)
    (hR : IsUnitary R) (hRs : star R = R) (hVN : Commute V (shift N))
    (hVP : Commute V (shift P)) (hRP : Commute R (shift P)) :
    ∃ (W : Op) (z : ℂ), IsUnitary (V*W) ∧ Commute (V*W) (shift P) ∧
      ‖V*W - V‖ < δ ∧ z ≠ 0 ∧ ‖readout (V*W) N z‖ ≤ 2 ∧
      ‖readout (V*W) N z - (shift N * R - R * shift N)‖ < 2*δ := by
  obtain ⟨W,z,hW,hz,he,hsmall⟩ := small_rotation R hR hRs δ hδ
  have hWW : Commute W (shift P) := by
    rw [he]
    exact (Commute.one_left _).add_left ((hRP.sub_left (Commute.one_left _)).smul_left z)
  have hdiff : V*W - V = V*(W-1) := by rw [mul_sub, mul_one]
  refine ⟨W,z, (unitary Op).mul_mem hV hW, hVP.mul_left hWW, ?_, hz, ?_⟩
  · rwa [hdiff, CStarRing.norm_mem_unitary_mul _ hV]
  rw [readout_rotation V W R N z hV hW hVN hz he]
  let C := shift N * R - R * shift N
  have hnormA (A : Op) (hA : IsUnitary A) : ‖A‖ ≤ 1 := by
    apply A.opNorm_le_bound zero_le_one
    intro x
    simp [unitary_norm A hA x]
  have hC : ‖C‖ ≤ 2 := by
    apply (norm_sub_le _ _).trans
    rw [CStarRing.norm_mem_unitary_mul _ (shift_unitary N), CStarRing.norm_mem_unitary_mul _ hR]
    linarith [hnormA R hR, hnormA _ (shift_unitary N)]
  change ‖star W * C‖ ≤ 2 ∧ ‖star W * C - C‖ < 2*δ
  constructor
  · rwa [CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem hW)]
  · have hs : ‖star W - 1‖ = ‖W-1‖ := by rw [← star_one (R := Op), ← star_sub, norm_star, star_one]
    calc
      ‖star W * C - C‖ = ‖(star W - 1)*C‖ := by rw [sub_mul, one_mul]
      _ ≤ ‖star W - 1‖ * ‖C‖ := norm_mul_le _ _
      _ ≤ ‖W - 1‖ * 2 := by rw [hs]; gcongr
      _ < 2 * δ := by linarith

end OperatorPhaseRetrieval.TwoUnitary
