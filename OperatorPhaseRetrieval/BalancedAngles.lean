module

public import OperatorPhaseRetrieval.MathlibImports
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

noncomputable section

namespace OperatorPhaseRetrieval

/-- Shifting finitely many principal angles by a single full turn bounds their
sum by pi while increasing each absolute angle to at most 3 pi. -/
theorem exists_balanced_angles (ι : Type*) [Fintype ι] (θ : ι → ℝ)
    (hθ : ∀ i, |θ i| ≤ Real.pi) :
    ∃ (φ : ι → ℝ) (k : ι → ℤ),
      (∀ i, φ i = θ i - 2 * Real.pi * (k i : ℝ)) ∧
      (∀ i, |φ i| ≤ 3 * Real.pi) ∧ |∑ i, φ i| ≤ Real.pi := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
    exact ⟨θ, fun _ => 0, by simp, by intro i; exact isEmptyElim i, by simp [Real.pi_nonneg]⟩
  | inr h =>
    let m := round ((∑ i, θ i) / (2 * Real.pi))
    have hp := Real.pi_pos
    have hn : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have hsum : |∑ i, θ i| ≤ (Fintype.card ι : ℝ) * Real.pi := by
      calc
        |∑ i, θ i| ≤ ∑ i, |θ i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ : ι, Real.pi := Finset.sum_le_sum (fun i _ => hθ i)
        _ = _ := by simp
    have hx : |(∑ i, θ i) / (2 * Real.pi)| ≤ (Fintype.card ι : ℝ) / 2 := by
      rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    have hr : |(∑ i, θ i) / (2 * Real.pi) - (m : ℝ)| ≤ 1 / 2 := abs_sub_round _
    have hm : |(m : ℝ)| ≤ (Fintype.card ι : ℝ) := by
      rw [abs_le] at hx hr ⊢
      constructor <;> linarith
    have hmNat : m.natAbs ≤ Fintype.card ι := by
      have hm' : (m.natAbs : ℝ) ≤ (Fintype.card ι : ℝ) := by
        simpa only [Nat.cast_natAbs, Int.cast_abs] using hm
      exact_mod_cast hm'
    obtain ⟨s, _, hs⟩ := Finset.exists_subset_card_eq (s := Finset.univ) hmNat
    let k : ι → ℤ := fun i => if i ∈ s then m.sign else 0
    let φ : ι → ℝ := fun i => θ i - 2 * Real.pi * (k i : ℝ)
    have hk (i : ι) : |(k i : ℝ)| ≤ 1 := by
      dsimp [k]
      split_ifs
      · have hsign := Int.sign_trichotomy m
        rcases hsign with h | h | h <;> simp [h]
      · simp
    refine ⟨φ, k, fun _ => rfl, ?_, ?_⟩
    · intro i
      dsimp [φ]
      calc
        |θ i - 2 * Real.pi * (k i : ℝ)| ≤ |θ i| + |2 * Real.pi * (k i : ℝ)| := abs_sub _ _
        _ ≤ 3 * Real.pi := by
          rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
          nlinarith [hθ i, hk i]
    · have hksum : ∑ i, k i = m := by
        simpa [k, hs, mul_comm] using Int.sign_mul_natAbs m
      have hφ : ∑ i, φ i = ∑ i, θ i - 2 * Real.pi * (m : ℝ) := by
        simp only [φ, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Int.cast_sum, hksum]
      rw [hφ]
      have he : (∑ i, θ i) - 2 * Real.pi * (m : ℝ) =
          (2 * Real.pi) * ((∑ i, θ i) / (2 * Real.pi) - (m : ℝ)) := by field_simp
      rw [he, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      nlinarith

end OperatorPhaseRetrieval

end
