module

public import OperatorPhaseRetrieval.MathlibImports
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Module
open scoped ENNReal NNReal Function

namespace OperatorPhaseRetrieval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The standard volumetric packing bound in the unit ball, with its exact
dimension dependence and arbitrary positive separation. -/
theorem separated_finset_card_le (s : Finset E) (hs : ∀ c ∈ s, ‖c‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε)
    (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → ε ≤ ‖c - d‖) :
    (s.card : ℝ) ≤ (1 + 2 / ε) ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ := ε / 2
  let ρ := 1 + ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let A := ⋃ c ∈ s, ball c δ
  have hdisj : Set.Pairwise (s : Set E) (Disjoint on fun c => ball c δ) := by
    intro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    dsimp [δ]
    linarith [hsep c hc d hd hcd]
  have hsub : A ⊆ ball (0 : E) ρ := by
    refine iUnion₂_subset fun c hc => ball_subset_ball' ?_
    rw [dist_zero_right]
    dsimp [δ, ρ]
    linarith [hs c hc]
  have hvol : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal (ρ ^ finrank ℝ E) * μ (ball 0 1) := by
    calc
      _ = μ A := by
        rw [show A = ⋃ c ∈ s, ball c δ from rfl,
          measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)]
        simp only [μ.addHaar_ball_of_pos _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) ρ) := measure_mono hsub
      _ = _ := μ.addHaar_ball_of_pos _ hρ
  have hj : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) ≤
      ENNReal.ofReal (ρ ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos μ (0 : E) zero_lt_one).ne'
      measure_ball_lt_top.ne).mp hvol
  have hjr : (s.card : ℝ) * δ ^ finrank ℝ E ≤ ρ ^ finrank ℝ E := by
    have h := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) hj
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal
      (pow_nonneg hδ.le _)] using h
  have hratio : ρ / δ = 1 + 2 / ε := by dsimp [ρ, δ]; field_simp; ring
  calc
    _ ≤ ρ ^ finrank ℝ E / δ ^ finrank ℝ E := (le_div_iff₀ (pow_pos hδ _)).mpr hjr
    _ = (ρ / δ) ^ finrank ℝ E := (div_pow _ _ _).symm
    _ = _ := by rw [hratio]

/-- A finite internal net in any subset of the unit ball, with the usual
volumetric cardinality bound. No closedness assumption on the subset is needed. -/
theorem exists_finset_unitBall_net (A : Set E) (hA : ∀ x ∈ A, ‖x‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset E, (∀ x ∈ s, x ∈ A) ∧
      (∀ x ∈ A, ∃ c ∈ s, ‖x - c‖ ≤ ε) ∧
      (s.card : ℝ) ≤ (1 + 2 / ε) ^ finrank ℝ E := by
  classical
  let P (s : Finset E) := (∀ x ∈ s, x ∈ A) ∧
    (∀ c ∈ s, ∀ d ∈ s, c ≠ d → ε ≤ ‖c - d‖)
  let C : Set ℕ := {n | ∃ s : Finset E, P s ∧ s.card = n}
  have hCne : C.Nonempty := ⟨0, ∅, by simp [P]⟩
  have hCbd : BddAbove C := by
    refine ⟨⌈(1 + 2 / ε) ^ finrank ℝ E⌉₊, ?_⟩
    rintro n ⟨s, hs, rfl⟩
    have h := separated_finset_card_le s (fun x hx => hA x (hs.1 x hx)) ε hε hs.2
    exact_mod_cast h.trans (Nat.le_ceil _)
  obtain ⟨s, hs, hcard⟩ := hCne.csSup_mem hCbd.finite
  have hmax (r : Finset E) (hr : P r) : r.card ≤ s.card := by
    rw [hcard]
    exact le_csSup hCbd ⟨r, hr, rfl⟩
  refine ⟨s, hs.1, ?_, separated_finset_card_le s (fun x hx => hA x (hs.1 x hx)) ε hε hs.2⟩
  intro x hx
  by_contra! hbad
  have hxnot : x ∉ s := by
    intro hxs
    have := hbad x hxs
    simp only [sub_self, norm_zero] at this
    linarith
  have hinsert : P (insert x s) := by
    constructor
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hx
      · exact hs.1 z hz
    · intro c hc d hd hcd
      rcases Finset.mem_insert.mp hc with rfl | hcs
      · rcases Finset.mem_insert.mp hd with rfl | hd
        · exact False.elim (hcd rfl)
        · exact (hbad d hd).le
      · rcases Finset.mem_insert.mp hd with rfl | hd
        · simpa only [norm_sub_rev] using (hbad c hcs).le
        · exact hs.2 c hcs d hd hcd
  have h := hmax (insert x s) hinsert
  rw [Finset.card_insert_of_notMem hxnot] at h
  omega

end OperatorPhaseRetrieval

end
