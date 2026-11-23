import Mathlib.Probability.Moments.Variance

noncomputable section

open MeasureTheory ProbabilityTheory

namespace OperatorPhaseRetrieval

variable {J : Type*} [Fintype J] {Ω : J → Type*} [∀ j, MeasurableSpace (Ω j)]
  (μ : (j : J) → Measure (Ω j)) [∀ j, IsProbabilityMeasure (μ j)]

/-- The mean of a sum of coordinate functions under a product probability measure. -/
theorem integral_sum_pi (X : (j : J) → Ω j → ℝ) (hX : ∀ j, Integrable (X j) (μ j)) :
    (∫ ω, ∑ j, X j (ω j) ∂Measure.pi μ) = ∑ j, ∫ x, X j x ∂μ j := by
  have hi (j : J) : Integrable (fun ω => X j (ω j)) (Measure.pi μ) :=
    (measurePreserving_eval μ j).integrable_comp_of_integrable (hX j)
  rw [integral_finsetSum _ (fun j _ => hi j)]
  apply Finset.sum_congr rfl
  intro j _
  have hm := measurePreserving_eval μ j
  have h := integral_map (μ := Measure.pi μ) hm.measurable.aemeasurable
    ((hX j).aestronglyMeasurable.mono_measure (by rw [hm.map_eq]))
  rw [hm.map_eq] at h
  exact h.symm

/-- The second moment of an independent sum is its summed variance plus squared mean. -/
theorem secondMoment_sum_pi (X : (j : J) → Ω j → ℝ) (hX : ∀ j, MemLp (X j) 2 (μ j)) :
    (∫ ω, (∑ j, X j (ω j)) ^ 2 ∂Measure.pi μ) =
      (∑ j, variance (X j) (μ j)) + (∑ j, ∫ x, X j x ∂μ j) ^ 2 := by
  have hm : MemLp (fun ω => ∑ j, X j (ω j)) 2 (Measure.pi μ) :=
    memLp_finsetSum _ (fun j _ => (hX j).comp_measurePreserving (measurePreserving_eval μ j))
  have hv : variance (fun ω => ∑ j, X j (ω j)) (Measure.pi μ) =
      ∑ j, variance (X j) (μ j) := by
    convert! variance_sum_pi hX
    simp
  rw [variance_eq_sub hm] at hv
  simp only [Pi.pow_apply] at hv
  rw [integral_sum_pi μ X (fun j => (hX j).integrable (by norm_num))] at hv
  linarith

/-- Cauchy--Schwarz controls the collective scalar part with no factor multiplying
its complementary trace-zero energy. -/
theorem central_mean_sum_sq_le (a b : J → ℝ) (n C : ℝ) (hn : 0 < n)
    (ha : (∑ j, a j ^ 2) ≤ C * n) :
    (∑ j, a j * b j / n) ^ 2 ≤ C * (∑ j, b j ^ 2 / n) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  have hs : (∑ j, a j * b j) ^ 2 ≤ (C * n) * ∑ j, b j ^ 2 :=
    hcs.trans (mul_le_mul_of_nonneg_right ha (Finset.sum_nonneg fun j _ => sq_nonneg _))
  rw [← Finset.sum_div, ← Finset.sum_div, div_pow]
  calc
    _ ≤ ((C * n) * ∑ j, b j ^ 2) / n ^ 2 := div_le_div_of_nonneg_right hs (sq_nonneg n)
    _ = _ := by field_simp

/-- Orthogonal scalar and trace-zero bounds combine across independent factors. -/
theorem secondMoment_sum_pi_le (X : (j : J) → Ω j → ℝ) (hX : ∀ j, MemLp (X j) 2 (μ j))
    (a b v : J → ℝ) (n C : ℝ) (hn : 0 < n)
    (hmean : ∀ j, (∫ x, X j x ∂μ j) = a j * b j / n)
    (hvar : ∀ j, variance (X j) (μ j) ≤ C * (v j - b j ^ 2 / n))
    (ha : (∑ j, a j ^ 2) ≤ C * n) :
    (∫ ω, (∑ j, X j (ω j)) ^ 2 ∂Measure.pi μ) ≤ C * ∑ j, v j := by
  rw [secondMoment_sum_pi μ X hX]
  simp_rw [hmean]
  calc
    _ ≤ (∑ j, C * (v j - b j ^ 2 / n)) + C * (∑ j, b j ^ 2 / n) :=
      add_le_add (Finset.sum_le_sum fun j _ => hvar j) (central_mean_sum_sq_le a b n C hn ha)
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_sub_distrib]; ring

end OperatorPhaseRetrieval

end
