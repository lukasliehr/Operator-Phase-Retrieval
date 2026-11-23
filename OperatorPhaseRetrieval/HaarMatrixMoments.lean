import OperatorPhaseRetrieval.HaarConjugation
import OperatorPhaseRetrieval.FourthPolarization

noncomputable section

open MeasureTheory NormedSpace
open scoped InnerProductSpace

namespace OperatorPhaseRetrieval

instance haarUnitaryProbability_isInvInvariant
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] :
    (haarUnitaryProbability E : Measure (HaarUnitary E)).IsInvInvariant := by
  constructor
  let : IsProbabilityMeasure (haarUnitaryProbability E : Measure (HaarUnitary E)).inv := by
    change IsProbabilityMeasure (Measure.map Inv.inv (haarUnitaryProbability E : Measure (HaarUnitary E)))
    exact Measure.isProbabilityMeasure_map measurable_inv.aemeasurable
  have : (haarUnitaryProbability E : Measure (HaarUnitary E)).inv.IsHaarMeasure := {}
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

variable (ι : Type*) [Fintype ι]

/-- Matrix entries of the canonical Haar operator in the standard orthonormal basis. -/
def haarEntry (U : HaarUnitary (EuclideanSpace ℂ ι)) (i j : ι) : ℂ :=
  ((U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (EuclideanSpace.basisFun ι ℂ j)) i

theorem haarUnitary_coordinate_continuous (x : EuclideanSpace ℂ ι) (i : ι) :
    Continuous (fun U : HaarUnitary (EuclideanSpace ℂ ι) =>
      ((U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) x) i) :=
  (PiLp.continuous_apply 2 (fun _ : ι => ℂ) i).comp
    (continuous_subtype_val.clm_apply continuous_const)

@[fun_prop]
theorem haarEntry_continuous (i j : ι) :
    Continuous (fun U : HaarUnitary (EuclideanSpace ℂ ι) => haarEntry ι U i j) :=
  haarUnitary_coordinate_continuous ι (EuclideanSpace.basisFun ι ℂ j) i

theorem haarUnitary_coordinate_moment_integrable (x : EuclideanSpace ℂ ι) (i : ι) (p : ℕ) :
    Integrable (fun U : HaarUnitary (EuclideanSpace ℂ ι) =>
      ‖((U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) x) i‖ ^ p)
      (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _) :=
  ((haarUnitary_coordinate_continuous ι x i).norm.pow p).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Right Haar invariance identifies scalar-coordinate moments for any two unit inputs. -/
theorem haarUnitary_coordinate_moment_unit_eq (i : ι) (p : ℕ)
    (x y : EuclideanSpace ℂ ι) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    (∫ U : HaarUnitary (EuclideanSpace ℂ ι),
      ‖((U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) x) i‖ ^ p
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) =
    (∫ U : HaarUnitary (EuclideanSpace ℂ ι),
      ‖((U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) y) i‖ ^ p
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) := by
  obtain ⟨P, hP⟩ := exists_unitary_map_unit_vector (EuclideanSpace ℂ ι) x y hx hy
  have hm := measurePreserving_mul_right
    (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure (HaarUnitary (EuclideanSpace ℂ ι))) P
  have hf : Measurable (fun U : HaarUnitary (EuclideanSpace ℂ ι) =>
      ‖((U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) x) i‖ ^ p) :=
    ((haarUnitary_coordinate_continuous ι x i).norm.pow p).measurable
  have h := integral_map
    (μ := (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure (HaarUnitary (EuclideanSpace ℂ ι))))
    hm.measurable.aemeasurable hf.aestronglyMeasurable
  rw [hm.map_eq] at h
  rw [h]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun U => by
    change ‖((U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
      ((P : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) x)) i‖ ^ p = _
    rw [hP]

theorem haarEntry_row_norm_sq (U : HaarUnitary (EuclideanSpace ℂ ι)) (i : ι) :
    ∑ j, ‖haarEntry ι U i j‖ ^ 2 = 1 := by
  let e := Unitary.linearIsometryEquiv U
  have he (j : ι) : ‖haarEntry ι U i j‖ = ‖(e.symm (EuclideanSpace.basisFun ι ℂ i)) j‖ := by
    have h := e.inner_map_map (e.symm (EuclideanSpace.basisFun ι ℂ i))
      (EuclideanSpace.basisFun ι ℂ j)
    rw [e.apply_symm_apply] at h
    change inner ℂ (EuclideanSpace.basisFun ι ℂ i)
      ((U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (EuclideanSpace.basisFun ι ℂ j)) = _ at h
    rw [EuclideanSpace.basisFun_inner] at h
    change ‖((U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
      (EuclideanSpace.basisFun ι ℂ j)) i‖ = _
    rw [h, norm_inner_symm, EuclideanSpace.basisFun_inner]
  simp_rw [he]
  rw [← PiLp.norm_sq_eq_of_L2 (fun _ : ι => ℂ), e.symm.norm_map]
  simp

/-- Homogeneity extends the unit-input fourth moment to every vector. -/
theorem haarUnitary_coordinate_fourthMoment_radial (x : EuclideanSpace ℂ ι) (i j : ι) :
    (∫ U : HaarUnitary (EuclideanSpace ℂ ι),
      ‖((U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) x) i‖ ^ 4
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) =
    ‖x‖ ^ 4 * (∫ U, ‖haarEntry ι U i j‖ ^ 4
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) := by
  by_cases hx : x = 0
  · simp [hx]
  have h := haarUnitary_coordinate_moment_unit_eq ι i 4 (normalize x)
    (EuclideanSpace.basisFun ι ℂ j) (norm_normalize_eq_one_iff.mpr hx) (by simp)
  have he (U : HaarUnitary (EuclideanSpace ℂ ι)) :
      ‖((U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) x) i‖ ^ 4 =
      ‖x‖ ^ 4 * ‖((U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (normalize x)) i‖ ^ 4 := by
    have hv : (U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) x =
        ‖x‖ • (U : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (normalize x) := by
      rw [← LinearMapClass.map_smul_of_tower, norm_smul_normalize]
    rw [hv, PiLp.smul_apply, norm_smul, Real.norm_of_nonneg (norm_nonneg _), mul_pow]
  simp_rw [he]
  rw [integral_const_mul, h]
  rfl

theorem haarEntry_phase_sum_fourthMoment (i j k : ι) (hjk : j ≠ k)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    (∫ U, ‖haarEntry ι U i j + ζ * haarEntry ι U i k‖ ^ 4
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) =
    4 * (∫ U, ‖haarEntry ι U i j‖ ^ 4
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) := by
  let x := EuclideanSpace.basisFun ι ℂ j + ζ • EuclideanSpace.basisFun ι ℂ k
  have hx2 : ‖x‖ ^ 2 = 2 := by
    dsimp [x]
    rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, (EuclideanSpace.basisFun ι ℂ).inner_eq_zero hjk]
    norm_num [norm_smul, hζ]
  have hx4 : ‖x‖ ^ 4 = 4 := by
    rw [show 4 = 2*2 by norm_num, pow_mul, hx2]
    norm_num
  have h := haarUnitary_coordinate_fourthMoment_radial ι x i j
  rw [hx4] at h
  simpa only [x, map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, haarEntry] using h

theorem haarEntry_norm_pow_mul_integrable (i j k l : ι) (p q : ℕ) :
    Integrable (fun U => ‖haarEntry ι U i j‖ ^ p * ‖haarEntry ι U k l‖ ^ q)
      (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _) :=
  (((haarUnitary_coordinate_continuous ι (EuclideanSpace.basisFun ι ℂ j) i).norm.pow p).mul
    ((haarUnitary_coordinate_continuous ι (EuclideanSpace.basisFun ι ℂ l) k).norm.pow q)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- In a fixed row, a diagonal fourth moment is twice any mixed second moment. -/
theorem haarEntry_fourthMoment_eq_two_mixed (i j k : ι) (hjk : j ≠ k) :
    (∫ U, ‖haarEntry ι U i j‖ ^ 4
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) =
    2 * (∫ U, ‖haarEntry ι U i j‖ ^ 2 * ‖haarEntry ι U i k‖ ^ 2
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) := by
  let μ := (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure (HaarUnitary (EuclideanSpace ℂ ι)))
  have hi (f : HaarUnitary (EuclideanSpace ℂ ι) → ℝ) (hf : Continuous f) :
      Integrable f μ := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he := haarUnitary_coordinate_moment_unit_eq ι i 4
    (EuclideanSpace.basisFun ι ℂ k) (EuclideanSpace.basisFun ι ℂ j) (by simp) (by simp)
  change (∫ U, ‖haarEntry ι U i k‖ ^ 4 ∂μ) = (∫ U, ‖haarEntry ι U i j‖ ^ 4 ∂μ) at he
  have h₁ := haarEntry_phase_sum_fourthMoment ι i j k hjk 1 (by simp)
  have h₂ := haarEntry_phase_sum_fourthMoment ι i j k hjk (-1) (by simp)
  have h₃ := haarEntry_phase_sum_fourthMoment ι i j k hjk Complex.I (by simp)
  have h₄ := haarEntry_phase_sum_fourthMoment ι i j k hjk (-Complex.I) (by simp)
  simp only [one_mul] at h₁
  simp only [neg_one_mul, ← sub_eq_add_neg] at h₂
  simp only [neg_mul, ← sub_eq_add_neg] at h₄
  have hh := integral_congr_ae (μ := μ) (Filter.Eventually.of_forall
    (fun U : HaarUnitary (EuclideanSpace ℂ ι) =>
      complex_four_phase_fourth (haarEntry ι U i j) (haarEntry ι U i k)))
  repeat rw [integral_add (hi _ (by fun_prop)) (hi _ (by fun_prop))] at hh
  simp only [mul_assoc, integral_const_mul] at hh
  rw [he] at hh
  dsimp only [μ] at hh
  rw [h₁, h₂, h₃, h₄] at hh
  linarith

/-- Taking the inverse transposes absolute values of matrix entries. -/
theorem haarEntry_inv_norm (U : HaarUnitary (EuclideanSpace ℂ ι)) (i j : ι) :
    ‖haarEntry ι U⁻¹ i j‖ = ‖haarEntry ι U j i‖ := by
  let e := Unitary.linearIsometryEquiv U
  have h := e.inner_map_map (e.symm (EuclideanSpace.basisFun ι ℂ j))
    (EuclideanSpace.basisFun ι ℂ i)
  rw [e.apply_symm_apply] at h
  rw [EuclideanSpace.basisFun_inner] at h
  change ‖(e.symm (EuclideanSpace.basisFun ι ℂ j)) i‖ = ‖(e (EuclideanSpace.basisFun ι ℂ i)) j‖
  rw [h, norm_inner_symm, EuclideanSpace.basisFun_inner]

theorem haarEntry_column_norm_sq (U : HaarUnitary (EuclideanSpace ℂ ι)) (j : ι) :
    ∑ i, ‖haarEntry ι U i j‖ ^ 2 = 1 := by
  simpa only [haarEntry_inv_norm] using haarEntry_row_norm_sq ι U⁻¹ j

theorem haarEntry_permutation_mul (p : Equiv.Perm ι)
    (U : HaarUnitary (EuclideanSpace ℂ ι)) (i j : ι) :
    haarEntry ι (permutationHaarUnitary ι p * U) i j = haarEntry ι U (p.symm i) j := by
  rfl

/-- Joint entry moments are invariant under a common permutation of their rows. -/
theorem haarEntry_mixedMoment_row_permutation (p : Equiv.Perm ι) (i j k l : ι) :
    (∫ U, ‖haarEntry ι U (p.symm i) j‖ ^ 2 * ‖haarEntry ι U (p.symm k) l‖ ^ 2
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) =
    (∫ U, ‖haarEntry ι U i j‖ ^ 2 * ‖haarEntry ι U k l‖ ^ 2
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) := by
  have hm := measurePreserving_mul_left
    (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure (HaarUnitary (EuclideanSpace ℂ ι)))
    (permutationHaarUnitary ι p)
  have hf : Measurable (fun U : HaarUnitary (EuclideanSpace ℂ ι) =>
      ‖haarEntry ι U i j‖ ^ 2 * ‖haarEntry ι U k l‖ ^ 2) := by fun_prop
  have h := integral_map
    (μ := (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure (HaarUnitary (EuclideanSpace ℂ ι))))
    hm.measurable.aemeasurable hf.aestronglyMeasurable
  rw [hm.map_eq] at h
  simpa only [haarEntry_permutation_mul] using h.symm

variable [Nonempty ι]

/-- Exact second moment of every Haar matrix entry. -/
theorem haarEntry_secondMoment (i j : ι) :
    (∫ U, ‖haarEntry ι U i j‖ ^ 2
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) = (Fintype.card ι : ℝ)⁻¹ := by
  classical
  have he (k : ι) : (∫ U, ‖haarEntry ι U i k‖ ^ 2
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) =
    (∫ U, ‖haarEntry ι U i j‖ ^ 2
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) :=
    haarUnitary_coordinate_moment_unit_eq ι i 2 _ _ (by simp) (by simp)
  have hs : (∑ k, ∫ U, ‖haarEntry ι U i k‖ ^ 2
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) = 1 := by
    have hi (k : ι) : Integrable (fun U => ‖haarEntry ι U i k‖ ^ 2)
        (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _) :=
      haarUnitary_coordinate_moment_integrable ι (EuclideanSpace.basisFun ι ℂ k) i 2
    rw [← integral_finsetSum _ (fun k _ => hi k)]
    simp_rw [haarEntry_row_norm_sq]
    simp
  simp_rw [he] at hs
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [← one_div]
  apply (eq_div_iff hn).mpr
  simpa only [mul_comm] using hs

/-- Exact fourth moment of every entry of an n-dimensional Haar unitary. -/
theorem haarEntry_fourthMoment (i j : ι) :
    (∫ U, ‖haarEntry ι U i j‖ ^ 4
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) =
    2 / ((Fintype.card ι : ℝ) * (Fintype.card ι + 1)) := by
  classical
  let μ := (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure (HaarUnitary (EuclideanSpace ℂ ι)))
  let A := ∫ U, ‖haarEntry ι U i j‖ ^ 4 ∂μ
  have hm (k : ι) : (∫ U, ‖haarEntry ι U i j‖ ^ 2 * ‖haarEntry ι U i k‖ ^ 2 ∂μ) =
      A/2 + if k = j then A/2 else 0 := by
    by_cases hk : k = j
    · subst k
      have he : (∫ U, ‖haarEntry ι U i j‖ ^ 2 * ‖haarEntry ι U i j‖ ^ 2 ∂μ) = A := by
        apply integral_congr_ae
        filter_upwards [] with U
        ring
      rw [he]
      simp
    · have he := haarEntry_fourthMoment_eq_two_mixed ι i j k (Ne.symm hk)
      change A = 2 * (∫ U, ‖haarEntry ι U i j‖ ^ 2 * ‖haarEntry ι U i k‖ ^ 2 ∂μ) at he
      simp only [hk, if_false, add_zero]
      linarith
  have hs : (∑ k, ∫ U, ‖haarEntry ι U i j‖ ^ 2 * ‖haarEntry ι U i k‖ ^ 2 ∂μ) =
      (Fintype.card ι : ℝ)⁻¹ := by
    rw [← integral_finsetSum _ (fun k _ => haarEntry_norm_pow_mul_integrable ι i j i k 2 2)]
    simp_rw [← Finset.mul_sum, haarEntry_row_norm_sq, mul_one]
    exact haarEntry_secondMoment ι i j
  simp only [hm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hs
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hn1 : (Fintype.card ι : ℝ) + 1 ≠ 0 := by positivity
  change A = _
  apply (eq_div_iff (mul_ne_zero hn hn1)).mpr
  have hs' := congrArg (fun r : ℝ => r * (Fintype.card ι : ℝ)) hs
  simp only [inv_mul_cancel₀ hn] at hs'
  nlinarith

/-- Exact mixed fourth moment for two different entries in the same row. -/
theorem haarEntry_row_mixedMoment (i j k : ι) (hjk : j ≠ k) :
    (∫ U, ‖haarEntry ι U i j‖ ^ 2 * ‖haarEntry ι U i k‖ ^ 2
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) =
    1 / ((Fintype.card ι : ℝ) * (Fintype.card ι + 1)) := by
  have h := haarEntry_fourthMoment_eq_two_mixed ι i j k hjk
  rw [haarEntry_fourthMoment] at h
  simp only [div_eq_mul_inv] at h ⊢
  linarith

/-- Exact mixed fourth moment for two different entries in the same column. -/
theorem haarEntry_column_mixedMoment (i k j : ι) (hik : i ≠ k) :
    (∫ U, ‖haarEntry ι U i j‖ ^ 2 * ‖haarEntry ι U k j‖ ^ 2
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) =
    1 / ((Fintype.card ι : ℝ) * (Fintype.card ι + 1)) := by
  have hm := Measure.measurePreserving_inv
    (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure (HaarUnitary (EuclideanSpace ℂ ι)))
  have hf : Measurable (fun U : HaarUnitary (EuclideanSpace ℂ ι) =>
      ‖haarEntry ι U i j‖ ^ 2 * ‖haarEntry ι U k j‖ ^ 2) := by fun_prop
  have h := integral_map
    (μ := (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure (HaarUnitary (EuclideanSpace ℂ ι))))
    hm.measurable.aemeasurable hf.aestronglyMeasurable
  rw [hm.map_eq] at h
  simp only [haarEntry_inv_norm] at h
  rw [h, haarEntry_row_mixedMoment ι j i k hik]

/-- Exact mixed fourth moment when both row and column indices differ. -/
theorem haarEntry_disjoint_mixedMoment (i j k l : ι) (hik : i ≠ k) (hjl : j ≠ l) :
    (∫ U, ‖haarEntry ι U i j‖ ^ 2 * ‖haarEntry ι U k l‖ ^ 2
      ∂(haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure _)) =
    1 / ((Fintype.card ι : ℝ) ^ 2 - 1) := by
  classical
  let μ := (haarUnitaryProbability (EuclideanSpace ℂ ι) : Measure (HaarUnitary (EuclideanSpace ℂ ι)))
  let C := ∫ U, ‖haarEntry ι U i j‖ ^ 2 * ‖haarEntry ι U k l‖ ^ 2 ∂μ
  let B := 1 / ((Fintype.card ι : ℝ) * (Fintype.card ι + 1))
  have hm (r : ι) : (∫ U, ‖haarEntry ι U i j‖ ^ 2 * ‖haarEntry ι U r l‖ ^ 2 ∂μ) =
      C + if r = i then B - C else 0 := by
    by_cases hr : r = i
    · subst r
      rw [haarEntry_row_mixedMoment ι i j l hjl]
      simp [B]
    · have h := haarEntry_mixedMoment_row_permutation ι (Equiv.swap k r) i j r l
      have hi : (Equiv.swap k r).symm i = i := by
        simp [Equiv.swap_apply_of_ne_of_ne hik (Ne.symm hr)]
      have hk : (Equiv.swap k r).symm r = k := by simp
      rw [hi, hk] at h
      simpa only [hr, if_false, add_zero] using h.symm
  have hs : (∑ r, ∫ U, ‖haarEntry ι U i j‖ ^ 2 * ‖haarEntry ι U r l‖ ^ 2 ∂μ) =
      (Fintype.card ι : ℝ)⁻¹ := by
    rw [← integral_finsetSum _ (fun r _ => haarEntry_norm_pow_mul_integrable ι i j r l 2 2)]
    simp_rw [← Finset.mul_sum, haarEntry_column_norm_sq, mul_one]
    exact haarEntry_secondMoment ι i j
  simp only [hm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hs
  have hnNat : 1 < Fintype.card ι := Fintype.one_lt_card_iff.mpr ⟨i, k, hik⟩
  have hn : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hnNat
  have hn0 : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  have hn1 : (Fintype.card ι : ℝ) + 1 ≠ 0 := by positivity
  have hnd : (Fintype.card ι : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  change C = _
  apply (eq_div_iff hnd).mpr
  dsimp [B] at hs
  field_simp at hs
  nlinarith

end OperatorPhaseRetrieval

end
