import OperatorPhaseRetrieval.DiagonalSmoothing

/-! # A complement diagonal in the same Hilbert basis

An explicit diagonal complement makes the two-dimensional invariant subspaces
of the sharpness argument available without an additional spectral assumption.
-/

noncomputable section

namespace OperatorPhaseRetrieval

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem continuousLinearMap_eq_of_hilbertBasis (b : HilbertBasis ℕ ℂ H)
    (S T : H →L[ℂ] H) (h : ∀ n, S (b n) = T (b n)) : S = T := by
  ext x
  have hs := (b.hasSum_repr x).mapL S
  have ht := (b.hasSum_repr x).mapL T
  simp only [map_smul, h] at hs ht
  exact hs.unique ht

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem sqrt_one_sub_sq_sub_one_bound {a : ℝ} (ha : |a| ≤ 1) :
    |Real.sqrt (1 - a ^ 2) - 1| ≤ |a| := by
  have hs : a ^ 2 ≤ 1 := by nlinarith [sq_abs a, abs_nonneg a]
  have hroot := Real.sq_sqrt (show 0 ≤ 1 - a ^ 2 by linarith)
  have hpos := Real.sqrt_nonneg (1 - a ^ 2)
  apply abs_le.mpr
  constructor
  · nlinarith [sq_abs a, abs_nonneg a, mul_nonneg hpos (abs_nonneg a)]
  · nlinarith [abs_nonneg a]

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem complementWeight_summable {w : ℕ → ℝ} (hw : Summable w)
    (hb : ∀ n, |w n| ≤ 1) : Summable (fun n => Real.sqrt (1 - w n ^ 2) - 1) := by
  exact hw.abs.of_norm_bounded (fun n => by
    simpa only [Real.norm_eq_abs] using sqrt_one_sub_sq_sub_one_bound (hb n))

def diagonalComplement (b : HilbertBasis ℕ ℂ H) (w : ℕ → ℝ) : H →L[ℂ] H :=
  1 + diagonalSmoothing b (fun n => Real.sqrt (1 - w n ^ 2) - 1)

theorem diagonalComplement_basis (b : HilbertBasis ℕ ℂ H) {w : ℕ → ℝ}
    (hw : Summable w) (hb : ∀ n, |w n| ≤ 1) (n : ℕ) :
    diagonalComplement b w (b n) = (Real.sqrt (1 - w n ^ 2) : ℂ) • b n := by
  rw [diagonalComplement, add_apply, one_apply_eq_self,
    diagonalSmoothing_basis b (complementWeight_summable hw hb) n]
  push_cast
  module

theorem diagonalComplement_selfAdjoint (b : HilbertBasis ℕ ℂ H) {w : ℕ → ℝ}
    (hw : Summable w) (hb : ∀ n, |w n| ≤ 1) : IsSelfAdjoint (diagonalComplement b w) :=
  (IsSelfAdjoint.one _).add (diagonalSmoothing_selfAdjoint b (complementWeight_summable hw hb))

theorem diagonalComplement_commute (b : HilbertBasis ℕ ℂ H) {w : ℕ → ℝ}
    (hw : Summable w) (hb : ∀ n, |w n| ≤ 1) :
    Commute (diagonalSmoothing b w) (diagonalComplement b w) := by
  apply continuousLinearMap_eq_of_hilbertBasis b
  intro n
  simp only [mul_apply_eq_comp, diagonalComplement_basis b hw hb,
    diagonalSmoothing_basis b hw, map_smul]
  exact smul_comm _ _ _

theorem diagonalComplement_sq (b : HilbertBasis ℕ ℂ H) {w : ℕ → ℝ}
    (hw : Summable w) (hb : ∀ n, |w n| ≤ 1) :
    diagonalSmoothing b w * diagonalSmoothing b w +
      diagonalComplement b w * diagonalComplement b w = 1 := by
  apply continuousLinearMap_eq_of_hilbertBasis b
  intro n
  have hs : (w n) ^ 2 ≤ 1 := by nlinarith [sq_abs (w n), abs_nonneg (w n), hb n]
  have he : (w n : ℂ) * (w n : ℂ) +
      (Real.sqrt (1 - w n ^ 2) : ℂ) * (Real.sqrt (1 - w n ^ 2) : ℂ) = 1 := by
    have hr := Real.sq_sqrt (show 0 ≤ 1 - w n ^ 2 by linarith)
    have hreal : w n * w n + Real.sqrt (1 - w n ^ 2) * Real.sqrt (1 - w n ^ 2) = 1 := by
      nlinarith
    exact_mod_cast hreal
  simp only [add_apply, mul_apply_eq_comp, one_apply_eq_self,
    diagonalSmoothing_basis b hw, diagonalComplement_basis b hw hb, map_smul,
    smul_smul, ← add_smul, he, one_smul]

end OperatorPhaseRetrieval

end
