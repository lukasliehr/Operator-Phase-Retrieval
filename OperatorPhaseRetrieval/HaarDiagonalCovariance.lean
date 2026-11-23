import OperatorPhaseRetrieval.HaarMatrixMoments

noncomputable section

open MeasureTheory

namespace OperatorPhaseRetrieval

/-- Summing a kernel with one diagonal and one off-diagonal value. -/
theorem sum_diagonal_kernel (ι : Type*) [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (D C : ℝ) :
    (∑ i, ∑ j, a i * b j * (if i = j then D else C)) =
    (D-C) * (∑ i, a i * b i) + C * (∑ i, a i) * (∑ j, b j) := by
  have he (i j : ι) : a i * b j * (if i = j then D else C) =
      (if j = i then (D-C) * (a i * b i) else 0) + C * a i * b j := by
    by_cases hij : i = j
    · subst j; simp; ring
    · simp only [hij, Ne.symm hij, if_false]; ring
  simp_rw [he, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.mul_sum,
    ← Finset.sum_mul]

variable (ι : Type*) [Fintype ι]

def haarDiagonal (a : ι → ℝ) (U : HaarUnitary (EuclideanSpace ℂ ι)) (i : ι) : ℝ :=
  ∑ j, a j * ‖haarEntry ι U i j‖ ^ 2

@[fun_prop]
theorem haarDiagonal_continuous (a : ι → ℝ) (i : ι) : Continuous (fun U => haarDiagonal ι a U i) := by
  unfold haarDiagonal
  fun_prop

/-- The diagonal of a random unitary conjugate has the normalized trace as its mean. -/
theorem haarDiagonal_mean [Nonempty ι] (a : ι → ℝ) (i : ι) :
    (∫ U, haarDiagonal ι a U i
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) =
      (∑ j, a j) / Fintype.card ι := by
  unfold haarDiagonal
  have hi (j : ι) : Integrable (fun U => a j * ‖haarEntry ι U i j‖ ^ 2)
      (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _) :=
    (haarUnitary_coordinate_moment_integrable ι (EuclideanSpace.basisFun ι ℂ j) i 2).const_mul (a j)
  rw [integral_finsetSum _ (fun j _ => hi j)]
  simp_rw [integral_const_mul, haarEntry_secondMoment]
  rw [← Finset.sum_mul, div_eq_mul_inv]

/-- Joint diagonal moments are finite sums of the already proved entry moments. -/
theorem haarDiagonal_mixedMoment_expansion (a b : ι → ℝ) (i k : ι) :
    (∫ U, haarDiagonal ι a U i * haarDiagonal ι b U k
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) =
    ∑ j, ∑ l, a j * b l * (∫ U, ‖haarEntry ι U i j‖ ^ 2 * ‖haarEntry ι U k l‖ ^ 2
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) := by
  have he (U : HaarUnitary (EuclideanSpace ℂ ι)) :
      haarDiagonal ι a U i * haarDiagonal ι b U k =
      ∑ j, ∑ l, (a j * b l) * (‖haarEntry ι U i j‖ ^ 2 * ‖haarEntry ι U k l‖ ^ 2) := by
    unfold haarDiagonal
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun l _ =>
    (haarEntry_norm_pow_mul_integrable ι i j k l 2 2).const_mul (a j * b l)))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum _ (fun l _ =>
    (haarEntry_norm_pow_mul_integrable ι i j k l 2 2).const_mul (a j * b l))]
  simp only [integral_const_mul]

variable [Nonempty ι]

/-- Trace-zero input gives an exact same-row covariance formula. -/
theorem haarDiagonal_sameRow_covariance (a b : ι → ℝ) (ha : ∑ j, a j = 0) (i : ι) :
    (∫ U, haarDiagonal ι a U i * haarDiagonal ι b U i
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) =
    (∑ j, a j * b j) / ((Fintype.card ι : ℝ) * (Fintype.card ι + 1)) := by
  classical
  have he (j l : ι) :
      (∫ U, ‖haarEntry ι U i j‖ ^ 2 * ‖haarEntry ι U i l‖ ^ 2
        ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) =
      if j = l then 2 / ((Fintype.card ι : ℝ) * (Fintype.card ι + 1))
      else 1 / ((Fintype.card ι : ℝ) * (Fintype.card ι + 1)) := by
    by_cases hjl : j = l
    · subst l
      simp only [if_true, ← pow_add, show 2 + 2 = 4 from rfl, haarEntry_fourthMoment]
    · simpa only [hjl, if_false] using haarEntry_row_mixedMoment ι i j l hjl
  rw [haarDiagonal_mixedMoment_expansion]
  simp_rw [he]
  rw [sum_diagonal_kernel, ha]
  simp only [mul_zero, zero_mul, add_zero]
  ring

/-- The covariances of different diagonal coordinates are negative for trace-zero inputs. -/
theorem haarDiagonal_differentRow_covariance (a b : ι → ℝ) (ha : ∑ j, a j = 0)
    (i k : ι) (hik : i ≠ k) :
    (∫ U, haarDiagonal ι a U i * haarDiagonal ι b U k
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) =
    -(∑ j, a j * b j) / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) ^ 2 - 1)) := by
  classical
  have he (j l : ι) :
      (∫ U, ‖haarEntry ι U i j‖ ^ 2 * ‖haarEntry ι U k l‖ ^ 2
        ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) =
      if j = l then 1 / ((Fintype.card ι : ℝ) * (Fintype.card ι + 1))
      else 1 / ((Fintype.card ι : ℝ) ^ 2 - 1) := by
    by_cases hjl : j = l
    · subst l
      simpa only [if_true] using haarEntry_column_mixedMoment ι i k j hik
    · simpa only [hjl, if_false] using haarEntry_disjoint_mixedMoment ι i j k l hik hjl
  rw [haarDiagonal_mixedMoment_expansion]
  simp_rw [he]
  rw [sum_diagonal_kernel, ha]
  simp only [mul_zero, zero_mul, add_zero]
  have hnNat : 1 < Fintype.card ι := Fintype.one_lt_card_iff.mpr ⟨i, k, hik⟩
  have hn : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hnNat
  have hn0 : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  have hn1 : (Fintype.card ι : ℝ) + 1 ≠ 0 := by positivity
  have hnd : (Fintype.card ι : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp
  ring

/-- The trace pairing of a diagonal test matrix with a Haar-conjugated diagonal matrix. -/
def haarDiagonalPairing (a b : ι → ℝ) (U : HaarUnitary (EuclideanSpace ℂ ι)) : ℝ :=
  ∑ i, b i * haarDiagonal ι a U i

omit [Nonempty ι] in
@[fun_prop]
theorem haarDiagonalPairing_continuous (a b : ι → ℝ) :
    Continuous (haarDiagonalPairing ι a b) := by
  unfold haarDiagonalPairing
  fun_prop

/-- The centered adjoint-orbit covariance, in diagonal coordinates. -/
theorem haarDiagonalPairing_covariance (a c b d : ι → ℝ) (ha : ∑ j, a j = 0)
    (hnNat : 1 < Fintype.card ι) :
    (∫ U, haarDiagonalPairing ι a b U * haarDiagonalPairing ι c d U
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) =
    ((∑ j, a j * c j) / ((Fintype.card ι : ℝ) ^ 2 - 1)) *
      ((∑ i, b i * d i) - (∑ i, b i) * (∑ i, d i) / Fintype.card ι) := by
  classical
  let μ := (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure (HaarUnitary (EuclideanSpace ℂ ι)))
  have hi (i k : ι) : Integrable (fun U => b i * d k *
      (haarDiagonal ι a U i * haarDiagonal ι c U k)) μ :=
    (by fun_prop : Continuous (fun U => b i * d k *
      (haarDiagonal ι a U i * haarDiagonal ι c U k))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have he (U : HaarUnitary (EuclideanSpace ℂ ι)) :
      haarDiagonalPairing ι a b U * haarDiagonalPairing ι c d U =
      ∑ i, ∑ k, b i * d k * (haarDiagonal ι a U i * haarDiagonal ι c U k) := by
    unfold haarDiagonalPairing
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hexpand : (∫ U, haarDiagonalPairing ι a b U * haarDiagonalPairing ι c d U ∂μ) =
      ∑ i, ∑ k, b i * d k * (∫ U, haarDiagonal ι a U i * haarDiagonal ι c U k ∂μ) := by
    simp_rw [he]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ => hi i k))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun k _ => hi i k)]
    simp only [integral_const_mul]
  have hc (i k : ι) : (∫ U, haarDiagonal ι a U i * haarDiagonal ι c U k ∂μ) =
      if i = k then (∑ j, a j * c j) / ((Fintype.card ι : ℝ) * (Fintype.card ι + 1))
      else -(∑ j, a j * c j) / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) ^ 2 - 1)) := by
    by_cases hik : i = k
    · subst k
      simpa only [if_true] using haarDiagonal_sameRow_covariance ι a c ha i
    · simpa only [hik, if_false] using haarDiagonal_differentRow_covariance ι a c ha i k hik
  rw [hexpand]
  simp_rw [hc]
  rw [sum_diagonal_kernel]
  have hn : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hnNat
  have hn0 : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  have hn1 : (Fintype.card ι : ℝ) + 1 ≠ 0 := by positivity
  have hnd : (Fintype.card ι : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp
  ring

/-- An adjoint-orbit second-moment bound with the crucial n-squared denominator. -/
theorem haarDiagonalPairing_secondMoment_le (a b : ι → ℝ) (ha : ∑ j, a j = 0)
    (hnNat : 1 < Fintype.card ι) :
    (∫ U, (haarDiagonalPairing ι a b U) ^ 2
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) ≤
    ((∑ j, (a j) ^ 2) / ((Fintype.card ι : ℝ) ^ 2 - 1)) * (∑ i, (b i) ^ 2) := by
  simp_rw [pow_two]
  rw [haarDiagonalPairing_covariance ι a a b b ha hnNat]
  simp only [pow_two]
  apply mul_le_mul_of_nonneg_left
  · exact sub_le_self _ (div_nonneg (mul_self_nonneg _) (Nat.cast_nonneg _))
  · have hn : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hnNat
    exact div_nonneg (Finset.sum_nonneg (fun j _ => mul_self_nonneg _)) (by nlinarith)

end OperatorPhaseRetrieval

end
