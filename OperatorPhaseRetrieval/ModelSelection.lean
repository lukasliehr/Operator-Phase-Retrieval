module

public import OperatorPhaseRetrieval.ExpressionBounds

@[expose] public section

/-!
# Simultaneous control of countably many moments

This is the probability-selection step in the proof of Theorem B. It takes moment estimates
and bounds for the two other exceptional events as explicit hypotheses; it does
not assume the existence of a stable unitary family.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace OperatorPhaseRetrieval

/-- The threshold for the fourth moment of the expression with index `r`. -/
def momentThreshold (r : ℕ) (M : ℝ≥0) : ℝ≥0 := 2 ^ (r + 5) * (1 + M)

theorem momentThreshold_pos (r : ℕ) (M : ℝ≥0) : 0 < momentThreshold r M := by
  unfold momentThreshold
  positivity

theorem momentThreshold_ratio_le (r : ℕ) (M : ℝ≥0) :
    M / momentThreshold r M ≤ (2⁻¹ : ℝ≥0) ^ (r + 5) := by
  apply (div_le_iff₀ (momentThreshold_pos r M)).mpr
  rw [momentThreshold, ← mul_assoc, ← mul_pow]
  norm_num

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem measure_moment_excess_le (F : Ω → ℝ≥0∞) (hF : AEMeasurable F P)
    (M : ℝ≥0) (hM : ∫⁻ x, F x ∂P ≤ M) (r : ℕ) :
    P {x | (momentThreshold r M : ℝ≥0∞) < F x} ≤ (2⁻¹ : ℝ≥0∞) ^ (r + 5) := by
  have hK : momentThreshold r M ≠ 0 := (momentThreshold_pos r M).ne'
  calc
    P {x | (momentThreshold r M : ℝ≥0∞) < F x} ≤
      P {x | (momentThreshold r M : ℝ≥0∞) ≤ F x} :=
        measure_mono (fun x (hx : (momentThreshold r M : ℝ≥0∞) < F x) => hx.le)
    _ ≤ (∫⁻ x, F x ∂P) / momentThreshold r M :=
      meas_ge_le_lintegral_div hF (by exact_mod_cast hK) ENNReal.coe_ne_top
    _ ≤ (M : ℝ≥0∞) / momentThreshold r M := ENNReal.div_le_div_right hM _
    _ = ↑(M / momentThreshold r M) := (ENNReal.coe_div hK).symm
    _ ≤ ↑((2⁻¹ : ℝ≥0) ^ (r + 5)) := ENNReal.coe_le_coe.mpr (momentThreshold_ratio_le r M)
    _ = _ := by simp [ENNReal.inv_pow]

theorem tsum_moment_failure_weights :
    ∑' r : ℕ, (2⁻¹ : ℝ≥0∞) ^ (r + 5) = 1 / 16 := by
  simp_rw [pow_add]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric_two]
  apply (ENNReal.toReal_eq_toReal_iff' (by simp [ENNReal.mul_eq_top]) (by simp)).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv]

/-- Countably many moment constraints fail with probability at most `1/16`. -/
theorem measure_exists_moment_excess_le (F : ℕ → Ω → ℝ≥0∞)
    (hF : ∀ r, AEMeasurable (F r) P) (M : ℕ → ℝ≥0)
    (hM : ∀ r, ∫⁻ x, F r x ∂P ≤ M r) :
    P {x | ∃ r, (momentThreshold r (M r) : ℝ≥0∞) < F r x} ≤ 1 / 16 := by
  rw [show {x | ∃ r, (momentThreshold r (M r) : ℝ≥0∞) < F r x} =
    ⋃ r, {x | (momentThreshold r (M r) : ℝ≥0∞) < F r x} by ext; simp]
  exact (measure_iUnion_le _).trans ((ENNReal.tsum_le_tsum fun r =>
    measure_moment_excess_le (F r) (hF r) (M r) (hM r) r).trans_eq tsum_moment_failure_weights)

/-- The three exceptional events of the selection step cannot cover the probability space. -/
theorem exists_simultaneously_good [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ≥0∞) (hF : ∀ r, AEMeasurable (F r) P)
    (M : ℕ → ℝ≥0) (hM : ∀ r, ∫⁻ x, F r x ∂P ≤ M r)
    (A B : Set Ω) (hA : P A ≤ 1 / 4) (hB : P B ≤ 1 / 8) :
    ∃ x, x ∉ A ∧ x ∉ B ∧ ∀ r, F r x ≤ momentThreshold r (M r) := by
  let E := {x | ∃ r, (momentThreshold r (M r) : ℝ≥0∞) < F r x}
  have hE : P E ≤ 1 / 16 := measure_exists_moment_excess_le F hF M hM
  have hsmall : P ((A ∪ B) ∪ E) < 1 := by
    calc
      _ ≤ P A + P B + P E := (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
      _ ≤ (1 / 4 : ℝ≥0∞) + 1 / 8 + 1 / 16 := add_le_add (add_le_add hA hB) hE
      _ < 1 := by
        apply (ENNReal.toReal_lt_toReal (by simp) (by simp)).mp
        norm_num [ENNReal.toReal_add, ENNReal.toReal_inv]
  have hnot : ((A ∪ B) ∪ E) ≠ univ := by
    intro he
    simp [he] at hsmall
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).mp hnot
  have hAx : x ∉ A := fun ha => hx (Or.inl (Or.inl ha))
  have hBx : x ∉ B := fun hb => hx (Or.inl (Or.inr hb))
  refine ⟨x, hAx, hBx, fun r => le_of_not_gt ?_⟩
  intro hr
  exact hx (Or.inr ⟨r, hr⟩)

/-- Select a strictly increasing sequence of dimensions and one realization in
each dimension, with all countably many moment bounds uniform in the sequence.
The hypotheses isolate the finite-dimensional and marginal-law estimates. -/
theorem select_increasing_models
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (F : ∀ n, ℕ → Ω n → ℝ≥0∞)
    (hF : ∀ n r, AEMeasurable (F n r) (P n))
    (M : ℕ → ℝ≥0) (hM : ∀ n r, ∫⁻ x, F n r x ∂P n ≤ M r)
    (A : ∀ n, Set (Ω n)) (hA : ∀ n, 50 ≤ n → P n (A n) ≤ 1 / 4)
    (B : ∀ n, ℕ → Set (Ω n))
    (hB : ∀ k, ∃ N, ∀ n, N ≤ n → P n (B n k) ≤ 1 / 8) :
    ∃ n : ℕ → ℕ, StrictMono n ∧ Filter.Tendsto n Filter.atTop Filter.atTop ∧
      ∃ x : ∀ k, Ω (n k), ∀ k,
        50 ≤ n k ∧ x k ∉ A (n k) ∧ x k ∉ B (n k) k ∧
          ∀ r, F (n k) r (x k) ≤ momentThreshold r (M r) := by
  classical
  choose N hN using hB
  let n : ℕ → ℕ := Nat.rec (max 50 (N 0))
    (fun k prev => max (prev + 1) (max 50 (N (k + 1))))
  have hn : StrictMono n := strictMono_nat_of_lt_succ fun k => by
    change n k < max (n k + 1) (max 50 (N (k + 1)))
    exact (Nat.lt_succ_self (n k)).trans_le (le_max_left _ _)
  have hbound : ∀ k, 50 ≤ n k ∧ N k ≤ n k := by
    intro k
    cases k with
    | zero => exact ⟨le_max_left _ _, le_max_right _ _⟩
    | succ k =>
      exact ⟨(le_max_left _ _).trans (le_max_right _ _),
        (le_max_right _ _).trans (le_max_right _ _)⟩
  have hex : ∀ k, ∃ x : Ω (n k), x ∉ A (n k) ∧ x ∉ B (n k) k ∧
      ∀ r, F (n k) r x ≤ momentThreshold r (M r) := by
    intro k
    exact exists_simultaneously_good (F (n k)) (hF (n k)) M (hM (n k))
      (A (n k)) (B (n k) k) (hA (n k) (hbound k).1)
      (hN k (n k) (hbound k).2)
  choose x hx using hex
  exact ⟨n, hn, hn.tendsto_atTop, x, fun k => ⟨(hbound k).1, hx k⟩⟩

end OperatorPhaseRetrieval

end
