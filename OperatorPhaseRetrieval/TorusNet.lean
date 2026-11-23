import OperatorPhaseRetrieval.SphereCaps
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Phase grids and conditional small-ball estimates

Construct a finite phase grid and prove the exact small-ball bound of Lemma 4.3
for uniform measure on the sphere in a fixed complex orthogonal complement.
The grid has at most `(13/t)^n` points; this larger grid still gives the paper's
constant `2^(11n)`. The Haar-frame identification is carried out in `HaarSmallBall.lean`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace OperatorPhaseRetrieval

theorem complex_phase_dist_le (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ ≤ |a - b| := by
  have he : Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I) =
      Complex.exp ((b : ℂ) * Complex.I) *
        (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

def phaseGridSize (t : ℝ) : ℕ := ⌊4 * Real.pi / t⌋₊ + 1

def phaseGridAngle (t : ℝ) (j : Fin (phaseGridSize t)) : ℝ := (j : ℝ) * t / 2 - Real.pi

theorem phaseGridSize_le (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1 / 12) :
    (phaseGridSize t : ℝ) ≤ 13 / t := by
  have hf := Nat.floor_le (show 0 ≤ 4 * Real.pi / t by positivity)
  have hp := Real.pi_lt_d2
  simp only [phaseGridSize, Nat.cast_add, Nat.cast_one]
  apply (le_div_iff₀ ht).mpr
  have hft := (le_div_iff₀ ht).mp hf
  nlinarith

theorem exists_phaseGridAngle (t θ : ℝ) (ht : 0 < t)
    (hθ0 : -Real.pi ≤ θ) (hθ1 : θ ≤ Real.pi) :
    ∃ j : Fin (phaseGridSize t), |θ - phaseGridAngle t j| ≤ t / 2 := by
  let x := 2 * (θ + Real.pi) / t
  have hx : 0 ≤ x := div_nonneg (mul_nonneg (by norm_num) (by linarith)) ht.le
  have hbound : x ≤ 4 * Real.pi / t := by
    apply div_le_div_of_nonneg_right _ ht.le
    linarith
  let j : Fin (phaseGridSize t) := ⟨⌊x⌋₊, by
    change ⌊x⌋₊ < ⌊4 * Real.pi / t⌋₊ + 1
    exact Nat.lt_succ_of_le (Nat.floor_le_floor hbound)⟩
  refine ⟨j, ?_⟩
  have hlo := Nat.floor_le hx
  have hhi := Nat.lt_floor_add_one x
  have hlo' := (le_div_iff₀ ht).mp hlo
  have hhi' := (div_lt_iff₀ ht).mp hhi
  change |θ - ((⌊x⌋₊ : ℝ) * t / 2 - Real.pi)| ≤ t / 2
  apply abs_le.mpr
  constructor <;> nlinarith

theorem exists_phaseGrid_near (t : ℝ) (ht : 0 < t) (z : ℂ) :
    ∃ j : Fin (phaseGridSize t),
      ‖Complex.exp ((Complex.arg z : ℂ) * Complex.I) -
        Complex.exp ((phaseGridAngle t j : ℂ) * Complex.I)‖ ≤ t / 2 := by
  obtain ⟨j, hj⟩ := exists_phaseGridAngle t (Complex.arg z) ht
    (Complex.neg_pi_lt_arg z).le (Complex.arg_le_pi z)
  exact ⟨j, (complex_phase_dist_le _ _).trans hj⟩

variable {ι : Type*} [Fintype ι]

def coordinateModulus (z : EuclideanSpace ℂ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => ‖z i‖)

def phaseTorusPoint (r : EuclideanSpace ℝ ι) (θ : ι → ℝ) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => (r i : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I))

theorem euclidean_norm_le_mul_of_coordinate_le (x : EuclideanSpace ℂ ι)
    (y : EuclideanSpace ℝ ι) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i, ‖x i‖ ≤ c * |y i|) : ‖x‖ ≤ c * ‖y‖ := by
  have hs : ‖x‖ ^ 2 ≤ (c * ‖y‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.real_norm_sq_eq,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc
      ‖x i‖ ^ 2 ≤ (c * |y i|) ^ 2 := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr (h i)
      _ = c ^ 2 * y i ^ 2 := by rw [mul_pow, sq_abs]
  exact (sq_le_sq₀ (norm_nonneg x) (mul_nonneg hc (norm_nonneg y))).mp hs

theorem phaseTorusPoint_dist_le (r : EuclideanSpace ℝ ι) (θ φ : ι → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i, ‖Complex.exp ((θ i : ℂ) * Complex.I) -
      Complex.exp ((φ i : ℂ) * Complex.I)‖ ≤ c) :
    dist (phaseTorusPoint r θ) (phaseTorusPoint r φ) ≤ c * ‖r‖ := by
  rw [dist_eq_norm]
  apply euclidean_norm_le_mul_of_coordinate_le _ r c hc
  intro i
  change ‖(r i : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I) -
    (r i : ℂ) * Complex.exp ((φ i : ℂ) * Complex.I)‖ ≤ _
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  nlinarith [h i, abs_nonneg (r i)]

theorem dist_phaseTorusPoint_arg (y : EuclideanSpace ℂ ι) (r : EuclideanSpace ℝ ι) :
    dist y (phaseTorusPoint r (fun i => Complex.arg (y i))) = dist (coordinateModulus y) r := by
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [dist_eq_norm, Real.dist_eq]
  change ‖y i - (r i : ℂ) * Complex.exp ((Complex.arg (y i) : ℂ) * Complex.I)‖ =
    |‖y i‖ - r i|
  conv_lhs => arg 1; arg 1; rw [← Complex.norm_mul_exp_arg_mul_I (y i)]
  rw [← sub_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]

/-- A concrete finite phase grid covers every vector whose coordinate magnitudes
are close to the prescribed radii. -/
theorem exists_phaseTorusPoint_near (r : EuclideanSpace ℝ ι) (t δ : ℝ)
    (ht : 0 < t) (y : EuclideanSpace ℂ ι) (hy : dist (coordinateModulus y) r ≤ δ) :
    ∃ j : ι → Fin (phaseGridSize t),
      dist y (phaseTorusPoint r (fun i => phaseGridAngle t (j i))) ≤ δ + t / 2 * ‖r‖ := by
  choose j hj using fun i => exists_phaseGrid_near t ht (y i)
  refine ⟨j, (dist_triangle y (phaseTorusPoint r (fun i => Complex.arg (y i))) _).trans ?_⟩
  apply add_le_add
  · rwa [dist_phaseTorusPoint_arg]
  · exact phaseTorusPoint_dist_le r _ _ (t / 2) (by positivity) hj

/-- Covering the small-modulus event by balls of radius `3t`. -/
theorem small_modulus_event_subset_phase_grid {E : Type*} (f : E → EuclideanSpace ℂ ι)
    (r : EuclideanSpace ℝ ι) (hr : ‖r‖ ≤ 2) (t : ℝ) (ht : 0 < t) :
    {y | dist (coordinateModulus (f y)) r ≤ 2 * t} ⊆
      ⋃ j : ι → Fin (phaseGridSize t),
        {y | dist (f y) (phaseTorusPoint r (fun i => phaseGridAngle t (j i))) ≤ 3 * t} := by
  intro y hy
  obtain ⟨j, hj⟩ := exists_phaseTorusPoint_near r t (2 * t) ht (f y) hy
  apply mem_iUnion.mpr
  refine ⟨j, ?_⟩
  change dist (f y) _ ≤ 3 * t
  nlinarith

/-- The conditional geometric small-ball estimate, with the sphere and measure
constructed explicitly. Applying it to Haar frames additionally requires proving
their conditional sphere law. -/
theorem uniformSphere_modulus_smallBall_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (f : E → EuclideanSpace ℂ ι) (hf : Isometry f)
    (r : EuclideanSpace ℝ ι) (hr : ‖r‖ ≤ 2) (t : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1 / 12) :
    (uniformSphere E : Measure (sphere (0 : E) 1))
      {y | dist (coordinateModulus (f (y : E))) r ≤ 2 * t} ≤
      ENNReal.ofReal ((13 / t) ^ Fintype.card ι *
        (12 * t) ^ (Module.finrank ℝ E - 1)) := by
  classical
  let μ : Measure (sphere (0 : E) 1) := uniformSphere E
  let balls : (ι → Fin (phaseGridSize t)) → Set (sphere (0 : E) 1) :=
    fun j => {y | dist (f (y : E)) (phaseTorusPoint r (fun i => phaseGridAngle t (j i))) ≤ 3 * t}
  have hcap (j : ι → Fin (phaseGridSize t)) :
      μ (balls j) ≤ ENNReal.ofReal ((12 * t) ^ (Module.finrank ℝ E - 1)) := by
    have h := uniformSphere_cap_le E f hf (phaseTorusPoint r (fun i => phaseGridAngle t (j i)))
      (3 * t) (by positivity) (by linarith)
    convert h using 1
    congr 2
    ring
  calc
    _ ≤ μ (⋃ j, balls j) := measure_mono (small_modulus_event_subset_phase_grid
      (fun y : sphere (0 : E) 1 => f (y : E)) r hr t ht)
    _ ≤ ∑ j, μ (balls j) := measure_iUnion_fintype_le μ balls
    _ ≤ ∑ _j : ι → Fin (phaseGridSize t),
        ENNReal.ofReal ((12 * t) ^ (Module.finrank ℝ E - 1)) :=
      Finset.sum_le_sum fun j _ => hcap j
    _ = ENNReal.ofReal ((phaseGridSize t : ℝ) ^ Fintype.card ι *
        (12 * t) ^ (Module.finrank ℝ E - 1)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow, ENNReal.ofReal_mul (by positivity : 0 ≤ (phaseGridSize t : ℝ) ^ Fintype.card ι),
        ENNReal.ofReal_pow (by positivity : 0 ≤ (phaseGridSize t : ℝ)), ENNReal.ofReal_natCast]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      gcongr
      exact phaseGridSize_le t ht ht1

theorem phase_grid_smallBall_constant (n : ℕ) (hn : 3 ≤ n) (t : ℝ) (ht : 0 < t) :
    (13 / t) ^ n * (12 * t) ^ (2 * n - 3) ≤ (2 : ℝ) ^ (11 * n) * t ^ (n - 3) := by
  have hcancel : 13 / t * (12 * t) = (156 : ℝ) := by field_simp; ring
  calc
    _ = (156 : ℝ) ^ n * (12 * t) ^ (n - 3) := by
      rw [show 2 * n - 3 = n + (n - 3) by omega, pow_add, ← mul_assoc, ← mul_pow, hcancel]
    _ = (156 : ℝ) ^ n * 12 ^ (n - 3) * t ^ (n - 3) := by rw [mul_pow]; ring
    _ ≤ (156 : ℝ) ^ n * 12 ^ n * t ^ (n - 3) := by gcongr <;> norm_num
    _ = (1872 : ℝ) ^ n * t ^ (n - 3) := by rw [← mul_pow]; norm_num
    _ ≤ (2048 : ℝ) ^ n * t ^ (n - 3) := by gcongr; norm_num
    _ = _ := by rw [pow_mul]; norm_num

/-- The exponent and constant of Lemma 4.3 on the actual uniform sphere of
a real space of dimension `2n-2`. The Haar-frame identification is separate. -/
theorem uniformSphere_modulus_smallBall_le_exp {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (hn : 3 ≤ Fintype.card ι) (hdim : Module.finrank ℝ E = 2 * Fintype.card ι - 2)
    (f : E → EuclideanSpace ℂ ι) (hf : Isometry f)
    (r : EuclideanSpace ℝ ι) (hr : ‖r‖ ≤ 2) (t : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1 / 12) :
    (uniformSphere E : Measure (sphere (0 : E) 1))
      {y | dist (coordinateModulus (f (y : E))) r ≤ 2 * t} ≤
      ENNReal.ofReal ((2 : ℝ) ^ (11 * Fintype.card ι) * t ^ (Fintype.card ι - 3)) := by
  apply (uniformSphere_modulus_smallBall_le f hf r hr t ht ht1).trans
  apply ENNReal.ofReal_le_ofReal
  rw [hdim, Nat.sub_sub]
  exact phase_grid_smallBall_constant (Fintype.card ι) hn t ht

theorem coordinateModulus_norm (z : EuclideanSpace ℂ ι) : ‖coordinateModulus z‖ = ‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.norm_sq_eq]
  rfl

theorem normalized_pair_coefficients (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a ^ 2 + b ^ 2 = 1) (ht : t ≤ 1 / 12) (hd : |a - b| ≤ t) :
    1 / 2 ≤ a ∧ 1 / 2 ≤ b ∧ a / b ≤ 2 := by
  have hd1 := (abs_le.mp hd).1
  have hd2 := (abs_le.mp hd).2
  have ha1 : 1 / 2 ≤ a := by
    by_contra! h
    have hb1 : b < 7 / 12 := by linarith
    nlinarith
  have hb1 : 1 / 2 ≤ b := by
    by_contra! h
    have ha2 : a < 7 / 12 := by linarith
    nlinarith
  refine ⟨ha1, hb1, (div_le_iff₀ (by linarith : 0 < b)).mpr ?_⟩
  have ha2 : a ≤ 1 := by nlinarith [sq_nonneg b]
  linarith

theorem scaled_modulus_event_subset {E : Type*} (f : E → EuclideanSpace ℂ ι)
    (x : EuclideanSpace ℂ ι) (a b t : ℝ) (hb : 1 / 2 ≤ b) (ht : 0 < t) :
    {y | dist (b • coordinateModulus (f y)) (a • coordinateModulus x) ≤ t} ⊆
      {y | dist (coordinateModulus (f y)) ((a / b) • coordinateModulus x) ≤ 2 * t} := by
  intro y hy
  have hb0 : 0 < b := by linarith
  have he : b • (coordinateModulus (f y) - (a / b) • coordinateModulus x) =
      b • coordinateModulus (f y) - a • coordinateModulus x := by
    rw [smul_sub, smul_smul, mul_div_cancel₀ _ hb0.ne']
  have hd : b * dist (coordinateModulus (f y)) ((a / b) • coordinateModulus x) ≤ t := by
    change ‖b • coordinateModulus (f y) - a • coordinateModulus x‖ ≤ t at hy
    rw [← he, norm_smul, Real.norm_of_nonneg hb0.le] at hy
    exact hy
  change dist (coordinateModulus (f y)) ((a / b) • coordinateModulus x) ≤ 2 * t
  nlinarith [dist_nonneg (x := coordinateModulus (f y)) (y := (a / b) • coordinateModulus x)]

/-- The weighted two-vector estimate on a sphere, including the case where
one of the two coefficients is too small for the event to occur. -/
theorem uniformSphere_scaled_modulus_smallBall {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (hn : 3 ≤ Fintype.card ι) (hdim : Module.finrank ℝ E = 2 * Fintype.card ι - 2)
    (f : E →ₗᵢ[ℝ] EuclideanSpace ℂ ι) (x : EuclideanSpace ℂ ι) (hx : ‖x‖ = 1)
    (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ^ 2 + b ^ 2 = 1)
    (ht : 0 < t) (ht1 : t ≤ 1 / 12) :
    (uniformSphere E : Measure (sphere (0 : E) 1))
      {y | dist (b • coordinateModulus (f (y : E))) (a • coordinateModulus x) ≤ t} ≤
      ENNReal.ofReal ((2 : ℝ) ^ (11 * Fintype.card ι) * t ^ (Fintype.card ι - 3)) := by
  by_cases h : ({y : sphere (0 : E) 1 |
    dist (b • coordinateModulus (f (y : E))) (a • coordinateModulus x) ≤ t} : Set _).Nonempty
  · obtain ⟨y, hy⟩ := h
    have hd : |a - b| ≤ t := by
      have hd := abs_norm_sub_norm_le (b • coordinateModulus (f (y : E))) (a • coordinateModulus x)
      rw [norm_smul, norm_smul, coordinateModulus_norm, coordinateModulus_norm,
        f.norm_map, show ‖(y : E)‖ = 1 by simp, hx,
        Real.norm_of_nonneg ha, Real.norm_of_nonneg hb, mul_one, mul_one] at hd
      rw [abs_sub_comm]
      exact hd.trans hy
    obtain ⟨_, hb1, hratio⟩ := normalized_pair_coefficients a b t ha hb hab ht1 hd
    have hr : ‖(a / b) • coordinateModulus x‖ ≤ 2 := by
      rw [norm_smul, coordinateModulus_norm, hx, mul_one,
        Real.norm_of_nonneg (div_nonneg ha hb)]
      exact hratio
    exact (measure_mono (scaled_modulus_event_subset
      (fun y : sphere (0 : E) 1 => f (y : E)) x a b t hb1 ht)).trans
        (uniformSphere_modulus_smallBall_le_exp hn hdim f f.isometry _ hr t ht ht1)
  · rw [Set.not_nonempty_iff_eq_empty.mp h, measure_empty]
    exact bot_le

theorem orthogonalComplement_real_finrank (x : EuclideanSpace ℂ ι) (hx : ‖x‖ = 1) :
    Module.finrank ℝ (ℂ ∙ x)ᗮ = 2 * (Fintype.card ι - 1) := by
  have hd := (ℂ ∙ x).finrank_add_finrank_orthogonal
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  rw [finrank_span_singleton hx0, finrank_euclideanSpace] at hd
  rw [← Module.finrank_mul_finrank ℝ ℂ (ℂ ∙ x)ᗮ, Complex.finrank_real_complex]
  congr 1
  omega

theorem orthogonalComplement_nontrivial (hn : 3 ≤ Fintype.card ι)
    (x : EuclideanSpace ℂ ι) (hx : ‖x‖ = 1) : Nontrivial (ℂ ∙ x)ᗮ :=
  Module.nontrivial_of_finrank_pos (R := ℝ) (by
    rw [orthogonalComplement_real_finrank x hx]
    omega)

/-- The small-ball bound for a uniform unit vector in the complex orthogonal
complement of a fixed unit vector, as used conditionally in Lemma 4.3. -/
theorem uniformSphere_orthogonal_modulus_smallBall (hn : 3 ≤ Fintype.card ι)
    (x : EuclideanSpace ℂ ι) (hx : ‖x‖ = 1)
    (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ^ 2 + b ^ 2 = 1)
    (ht : 0 < t) (ht1 : t ≤ 1 / 12) :
    letI : InnerProductSpace ℝ (ℂ ∙ x)ᗮ := InnerProductSpace.rclikeToReal ℂ (ℂ ∙ x)ᗮ
    letI := orthogonalComplement_nontrivial hn x hx
    (uniformSphere (ℂ ∙ x)ᗮ : Measure (sphere (0 : (ℂ ∙ x)ᗮ) 1))
      {y | dist (b • coordinateModulus ((y : (ℂ ∙ x)ᗮ) : EuclideanSpace ℂ ι))
        (a • coordinateModulus x) ≤ t} ≤
      ENNReal.ofReal ((2 : ℝ) ^ (11 * Fintype.card ι) * t ^ (Fintype.card ι - 3)) := by
  let : InnerProductSpace ℝ (ℂ ∙ x)ᗮ := InnerProductSpace.rclikeToReal ℂ (ℂ ∙ x)ᗮ
  let := orthogonalComplement_nontrivial hn x hx
  let f : (ℂ ∙ x)ᗮ →ₗᵢ[ℝ] EuclideanSpace ℂ ι :=
    { toLinearMap := (ℂ ∙ x)ᗮ.subtype.restrictScalars ℝ, norm_map' := fun _ => rfl }
  have hd : Module.finrank ℝ (ℂ ∙ x)ᗮ = 2 * Fintype.card ι - 2 := by
    rw [orthogonalComplement_real_finrank x hx]
    omega
  exact uniformSphere_scaled_modulus_smallBall hn hd f x hx a b t ha hb hab ht ht1

end OperatorPhaseRetrieval

end
