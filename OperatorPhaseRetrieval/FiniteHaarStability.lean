import OperatorPhaseRetrieval.PairModulus
import OperatorPhaseRetrieval.VolumetricNet

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace OperatorPhaseRetrieval

variable (ι : Type*) [Fintype ι]

def haarFiveProbability : ProbabilityMeasure (Fin 5 → HaarUnitary (EuclideanSpace ℂ ι)) :=
  ⟨Measure.pi (fun _ : Fin 5 => (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)),
    inferInstance⟩

variable {ι}

theorem haarFive_point_failure_le (hn : 3 ≤ Fintype.card ι)
    (p : UnitaryPair ι) (hp : p ∈ normalizedOrthogonalPairs)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1 / 12) :
    (haarFiveProbability ι : Measure (Fin 5 → HaarUnitary (EuclideanSpace ℂ ι))) {U | ∀ j, pairModulusDistance (U j) p ≤ t} ≤
      ENNReal.ofReal (((2 : ℝ) ^ (11 * Fintype.card ι) * t ^ (Fintype.card ι - 3)) ^ 5) := by
  let μ : Measure (HaarUnitary (EuclideanSpace ℂ ι)) := haarUnitaryProbability (EuclideanSpace ℂ ι)
  let A : Set (HaarUnitary (EuclideanSpace ℂ ι)) := {u | pairModulusDistance u p ≤ t}
  have hA : μ A ≤ ENNReal.ofReal ((2 : ℝ) ^ (11 * Fintype.card ι) * t ^ (Fintype.card ι - 3)) :=
    haarUnitary_smallBall hn p.fst p.snd hp.1 hp.2 t ht ht1
  change Measure.pi (fun _ : Fin 5 => μ) {U | ∀ j, U j ∈ A} ≤ _
  have he : {U : Fin 5 → HaarUnitary (EuclideanSpace ℂ ι) | ∀ j, U j ∈ A} =
      univ.pi (fun _ => A) := by ext; simp
  rw [he, Measure.pi_pi]
  calc
    _ ≤ ∏ _j : Fin 5, ENNReal.ofReal ((2 : ℝ) ^ (11 * Fintype.card ι) * t ^ (Fintype.card ι - 3)) :=
      Finset.prod_le_prod' (fun _ _ => hA)
    _ = _ := by simp [ENNReal.ofReal_pow (by positivity : 0 ≤ (2 : ℝ) ^ (11 * Fintype.card ι) * t ^ (Fintype.card ι - 3))]

theorem haarFive_finite_failure_le (hn : 3 ≤ Fintype.card ι) (s : Finset (UnitaryPair ι))
    (hs : ∀ p ∈ s, p ∈ normalizedOrthogonalPairs)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1 / 12) :
    (haarFiveProbability ι : Measure (Fin 5 → HaarUnitary (EuclideanSpace ℂ ι)))
      (⋃ p ∈ s, {U | ∀ j, pairModulusDistance (U j) p ≤ t}) ≤
      ENNReal.ofReal ((s.card : ℝ) *
        ((2 : ℝ) ^ (11 * Fintype.card ι) * t ^ (Fintype.card ι - 3)) ^ 5) := by
  calc
    _ ≤ ∑ p ∈ s, (haarFiveProbability ι : Measure (Fin 5 → HaarUnitary (EuclideanSpace ℂ ι)))
        {U | ∀ j, pairModulusDistance (U j) p ≤ t} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ s, ENNReal.ofReal
        (((2 : ℝ) ^ (11 * Fintype.card ι) * t ^ (Fintype.card ι - 3)) ^ 5) :=
      Finset.sum_le_sum fun p hp => haarFive_point_failure_le hn p (hs p hp) t ht ht1
    _ = _ := by simp [ENNReal.ofReal_mul (Nat.cast_nonneg s.card)]

theorem normalized_failure_subset_finite (s : Finset (UnitaryPair ι))
    (ε t : ℝ) (hε : Real.sqrt 2 * ε ≤ t / 2)
    (hs : ∀ p ∈ normalizedOrthogonalPairs (ι := ι), ∃ q ∈ s, ‖p - q‖ ≤ ε) :
    {U : Fin 5 → HaarUnitary (EuclideanSpace ℂ ι) |
      ∃ p ∈ normalizedOrthogonalPairs, ∀ j, pairModulusDistance (U j) p < t / 2} ⊆
      ⋃ q ∈ s, {U | ∀ j, pairModulusDistance (U j) q ≤ t} := by
  rintro U ⟨p, hp, hbad⟩
  obtain ⟨q, hq, hpq⟩ := hs p hp
  refine mem_iUnion.mpr ⟨q, mem_iUnion.mpr ⟨hq, ?_⟩⟩
  intro j
  have h := pairModulusDistance_lipschitz (U j) q p
  rw [norm_sub_rev q p] at h
  have hbound := mul_le_mul_of_nonneg_left hpq (Real.sqrt_nonneg (2 : ℝ))
  have hdiff := (abs_le.mp h).2
  have hj := hbad j
  linarith

theorem haarFive_normalized_failure_le (hn : 3 ≤ Fintype.card ι)
    (ε t : ℝ) (hε : 0 < ε) (ht : 0 < t) (ht1 : t ≤ 1 / 12)
    (hεt : Real.sqrt 2 * ε ≤ t / 2) :
    (haarFiveProbability ι : Measure (Fin 5 → HaarUnitary (EuclideanSpace ℂ ι)))
      {U | ∃ p ∈ normalizedOrthogonalPairs, ∀ j, pairModulusDistance (U j) p < t / 2} ≤
      ENNReal.ofReal ((1 + 2 / ε) ^ (4 * Fintype.card ι) *
        ((2 : ℝ) ^ (11 * Fintype.card ι) * t ^ (Fintype.card ι - 3)) ^ 5) := by
  obtain ⟨s, hs, hcover, hcard⟩ := exists_finset_unitBall_net (E := UnitaryPair ι) (normalizedOrthogonalPairs (ι := ι))
    (fun p hp => (normalizedOrthogonalPairs_norm p hp).le) ε hε
  have h := (measure_mono (normalized_failure_subset_finite s ε t hεt hcover)).trans
    (haarFive_finite_failure_le hn s hs t ht ht1)
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  rw [unitaryPair_real_finrank] at hcard
  gcongr

theorem finite_net_failure_constant (n : ℕ) (hn : 15 ≤ n) (t : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1 / 12) :
    (1 + 2 / (t / (2 * Real.sqrt 2))) ^ (4 * n) *
        ((2 : ℝ) ^ (11 * n) * t ^ (n - 3)) ^ 5 ≤
      (2 : ℝ) ^ (67 * n) * t ^ (n - 15) := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsl : Real.sqrt 2 ≤ 3 / 2 := by nlinarith
  have hgrid : 1 + 2 / (t / (2 * Real.sqrt 2)) ≤ 7 / t := by
    apply (le_div_iff₀ ht).mpr
    have he : (1 + 2 / (t / (2 * Real.sqrt 2))) * t = t + 4 * Real.sqrt 2 := by
      field_simp
      ring
    rw [he]
    linarith
  have htpow : (t ^ (n - 3)) ^ 5 = t ^ (4 * n) * t ^ (n - 15) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have htwo : ((2 : ℝ) ^ (11 * n)) ^ 5 = 2 ^ (55 * n) := by
    rw [← pow_mul]
    congr 1
    omega
  calc
    _ ≤ (7 / t) ^ (4 * n) * ((2 : ℝ) ^ (11 * n) * t ^ (n - 3)) ^ 5 := by gcongr
    _ = ((7 : ℝ) ^ 4) ^ n * 2 ^ (55 * n) * t ^ (n - 15) := by
      rw [div_pow, mul_pow, htwo, htpow, pow_mul 7 4 n]
      field_simp
    _ ≤ ((2 : ℝ) ^ 12) ^ n * 2 ^ (55 * n) * t ^ (n - 15) := by gcongr; norm_num
    _ = _ := by rw [← pow_mul, ← pow_add]; congr 2; omega

theorem finite_net_failure_at_dyadic_scale (n : ℕ) (hn : 15 ≤ n) :
    (2 : ℝ) ^ (67 * n) * ((2 : ℝ) ^ (-99 : ℤ)) ^ (n - 15) =
      (2 : ℝ) ^ (1485 - 32 * (n : ℤ)) := by
  have hcast : ((n - 15 : ℕ) : ℤ) = (n : ℤ) - 15 := by omega
  calc
    _ = (2 : ℝ) ^ ((67 * n : ℕ) : ℤ) *
        (2 : ℝ) ^ ((-99 : ℤ) * ((n - 15 : ℕ) : ℤ)) := by
      rw [zpow_mul]
      simp only [zpow_natCast]
    _ = (2 : ℝ) ^ (((67 * n : ℕ) : ℤ) + (-99 : ℤ) * ((n - 15 : ℕ) : ℤ)) := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    _ = _ := by rw [hcast]; push_cast; congr 1; ring

/-- The failure probability and stability constant in Proposition 4.4, for
normalized orthogonal pairs. -/
theorem haarFive_normalized_failure_dyadic (hn : 50 ≤ Fintype.card ι) :
    (haarFiveProbability ι : Measure (Fin 5 → HaarUnitary (EuclideanSpace ℂ ι)))
      {U | ∃ p ∈ normalizedOrthogonalPairs, ∀ j,
        pairModulusDistance (U j) p < (2 : ℝ) ^ (-100 : ℤ)} ≤
      ENNReal.ofReal ((2 : ℝ) ^ (1485 - 32 * (Fintype.card ι : ℤ))) := by
  let t : ℝ := 2 ^ (-99 : ℤ)
  let ε : ℝ := t / (2 * Real.sqrt 2)
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 / 12 := by norm_num [t]
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hε : 0 < ε := div_pos ht (by positivity)
  have hεt : Real.sqrt 2 * ε ≤ t / 2 := by
    dsimp [ε]
    apply le_of_eq
    field_simp
  have hhalf : t / 2 = (2 : ℝ) ^ (-100 : ℤ) := by norm_num [t]
  have h := haarFive_normalized_failure_le (by omega : 3 ≤ Fintype.card ι) ε t hε ht ht1 hεt
  rw [hhalf] at h
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (2 : ℝ) ^ (67 * Fintype.card ι) * t ^ (Fintype.card ι - 15) :=
      finite_net_failure_constant (Fintype.card ι) (by omega) t ht ht1
    _ = _ := finite_net_failure_at_dyadic_scale (Fintype.card ι) (by omega)

theorem exists_five_normalized_stable (hn : 50 ≤ Fintype.card ι) :
    ∃ U : Fin 5 → HaarUnitary (EuclideanSpace ℂ ι),
      ∀ p ∈ normalizedOrthogonalPairs, ∃ j,
        (2 : ℝ) ^ (-100 : ℤ) ≤ pairModulusDistance (U j) p := by
  classical
  let A : Set (Fin 5 → HaarUnitary (EuclideanSpace ℂ ι)) :=
    {U | ∃ p ∈ normalizedOrthogonalPairs, ∀ j,
      pairModulusDistance (U j) p < (2 : ℝ) ^ (-100 : ℤ)}
  have hprob := haarFive_normalized_failure_dyadic hn
  have hB : ENNReal.ofReal ((2 : ℝ) ^ (1485 - 32 * (Fintype.card ι : ℤ))) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    exact zpow_lt_one_of_neg₀ (by norm_num) (by omega)
  have hne : ∃ U, U ∉ A := by
    by_contra! h
    have he : A = univ := Set.eq_univ_of_forall h
    change (haarFiveProbability ι : Measure _) A ≤ _ at hprob
    rw [he, measure_univ] at hprob
    exact (not_le_of_gt hB) hprob
  obtain ⟨U, hU⟩ := hne
  refine ⟨U, ?_⟩
  intro p hp
  by_contra! hbad
  exact hU ⟨p, hp, hbad⟩

end OperatorPhaseRetrieval

end
