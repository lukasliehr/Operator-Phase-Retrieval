import OperatorPhaseRetrieval.TwoUnitaryFourier

/-! Bounded convergence of Fourier matrix entries and recovery of a vector from its Gram matrix. -/
noncomputable section

open Filter Set
open scoped InnerProductSpace ComplexConjugate Topology
namespace OperatorPhaseRetrieval.TwoUnitary

private def matrixUnit (i j : ℤ) : Op := InnerProductSpace.rankOne ℂ (basis i) (basis j)

private theorem entry_matrixUnit (i j a b : ℤ) :
    entry (matrixUnit i j) a b = if a = i ∧ b = j then 1 else 0 := by
  have orth := orthonormal_iff_ite.mp basis.orthonormal
  simp only [entry, matrixUnit, InnerProductSpace.rankOne_apply, inner_smul_right, orth]
  split_ifs <;> simp_all

private theorem quad_matrixUnit (i j : ℤ) (h : H) :
    quad (matrixUnit i j) h = conj (basis.repr h i) * basis.repr h j := by
  simp only [quad, matrixUnit, InnerProductSpace.rankOne_apply, inner_smul_right,
    HilbertBasis.repr_apply_apply, inner_conj_symm]
  ring

private theorem norm_matrixUnit (i j : ℤ) : ‖matrixUnit i j‖ = 1 := by
  rw [matrixUnit, InnerProductSpace.norm_rankOne, basis.orthonormal.norm_eq_one,
    basis.orthonormal.norm_eq_one, one_mul]

private abbrev fourierSpan := Submodule.span ℂ (Set.range ⇑basis)

private theorem tendsto_on_span (A : ℕ → Op) (E : Op)
    (he : ∀ a b, Tendsto (fun n => entry (A n) a b) atTop (𝓝 (entry E a b)))
    {x y : H} (hx : x ∈ fourierSpan) (hy : y ∈ fourierSpan) :
    Tendsto (fun n => inner ℂ x (A n y)) atTop (𝓝 (inner ℂ x (E y))) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a,rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨b,rfl⟩ := hy; exact he a b
    | zero => simp
    | add x y _ _ hx hy => simpa only [map_add, inner_add_right] using hx.add hy
    | smul c y _ hy =>
      simpa only [map_smul, inner_smul_right] using hy.const_mul c
  | zero => simp
  | add x y _ _ hx hy => simpa only [inner_add_left] using hx.add hy
  | smul c x _ hx => simpa only [inner_smul_left] using hx.const_mul (conj c)

private theorem quad_diff_le (B : Op) (h p : H) :
    ‖quad B h - quad B p‖ ≤ ‖B‖ * ‖h-p‖ * (‖h‖ + ‖p‖) := by
  have hid : quad B h - quad B p = inner ℂ (h-p) (B h) + inner ℂ p (B (h-p)) := by
    simp only [quad, map_sub, inner_sub_left, inner_sub_right]
    abel
  rw [hid]
  calc
    _ ≤ ‖inner ℂ (h-p) (B h)‖ + ‖inner ℂ p (B (h-p))‖ := norm_add_le _ _
    _ ≤ ‖h-p‖ * ‖B h‖ + ‖p‖ * ‖B (h-p)‖ :=
      add_le_add (norm_inner_le_norm ..) (norm_inner_le_norm ..)
    _ ≤ ‖h-p‖ * (‖B‖ * ‖h‖) + ‖p‖ * (‖B‖ * ‖h-p‖) := by
      gcongr <;> apply B.le_opNorm
    _ = _ := by ring

/-- Uniformly bounded readouts converging on all Fourier matrix entries recover one Gram entry. -/
theorem tendsto_quad_of_entries (A : ℕ → Op) (i j : ℤ) (hA : ∀ n, ‖A n‖ ≤ 3)
    (he : ∀ a b, Tendsto (fun n => entry (A n) a b) atTop
      (𝓝 (if a = i ∧ b = j then 1 else 0))) (h : H) :
    Tendsto (fun n => quad (A n) h) atTop (𝓝 (conj (basis.repr h i) * basis.repr h j)) := by
  let E := matrixUnit i j
  rw [← quad_matrixUnit]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := min 1 (ε / (8 * (2 * ‖h‖ + 1)))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hc : h ∈ closure (fourierSpan : Set H) := by
    change h ∈ fourierSpan.topologicalClosure
    rw [basis.dense_span]
    trivial
  obtain ⟨p,hp,hph⟩ := Metric.mem_closure_iff.mp hc δ hδ
  rw [dist_eq_norm] at hph
  have hsmall : ‖h-p‖ < 1 := hph.trans_le (min_le_left ..)
  have hnorm : ‖p‖ ≤ ‖h‖ + 1 := by
    linarith [norm_sub_norm_le h p, neg_le_abs (‖h‖-‖p‖), abs_norm_sub_norm_le h p]
  have hsmall' : ‖h-p‖ * (8 * (2 * ‖h‖ + 1)) < ε :=
    (lt_div_iff₀ (by positivity)).mp (hph.trans_le (min_le_right ..))
  have hs := tendsto_on_span A E (fun a b => by simpa only [E, entry_matrixUnit] using he a b) hp hp
  filter_upwards [Metric.tendsto_nhds.mp hs (ε/2) (by positivity)] with n hn
  rw [dist_eq_norm] at hn ⊢
  let B := A n - E
  have hB : ‖B‖ ≤ 4 := (norm_sub_le ..).trans (by
    rw [show ‖E‖ = 1 from norm_matrixUnit i j]
    linarith [hA n])
  have hid (v : H) : quad B v = quad (A n) v - quad E v := by
    simp [quad, B, inner_sub_right]
  change ‖quad (A n) h - quad E h‖ < ε
  rw [← hid]
  have hpbound : ‖quad B p‖ < ε/2 := by rw [hid]; exact hn
  have err : ‖quad B h - quad B p‖ < ε/2 := calc
    _ ≤ ‖B‖ * ‖h-p‖ * (‖h‖ + ‖p‖) := quad_diff_le B h p
    _ ≤ 4 * ‖h-p‖ * (‖h‖ + (‖h‖ + 1)) := by gcongr
    _ < ε/2 := by linarith only [hsmall']
  linarith [norm_le_norm_sub_add (quad B h) (quad B p)]

/-- A row of the Gram matrix at any nonzero coefficient determines all other coefficients. -/
theorem phase_of_gram {f g : H}
    (h : ∀ i j, conj (basis.repr f i) * basis.repr f j =
      conj (basis.repr g i) * basis.repr g j) : ∃ c : Circle, g = c • f := by
  have hn (i : ℤ) : ‖basis.repr f i‖ = ‖basis.repr g i‖ := by
    have hs := congrArg norm (h i i)
    simp only [norm_mul, Complex.norm_conj] at hs
    nlinarith [norm_nonneg (basis.repr f i), norm_nonneg (basis.repr g i)]
  by_cases hz : ∀ i : ℤ, basis.repr f i = 0
  · refine ⟨1, ?_⟩
    rw [one_smul]
    apply basis.repr.injective
    ext i
    rw [hz, ← norm_eq_zero]
    simp [← hn, hz]
  · push Not at hz
    obtain ⟨p,hp⟩ := hz
    let phase := basis.repr g p / basis.repr f p
    have hu : ‖phase‖ = 1 := by
      rw [norm_div, ← hn, div_self (norm_ne_zero_iff.mpr hp)]
    let c : Circle := ⟨phase, mem_sphere_zero_iff_norm.mpr hu⟩
    refine ⟨c, ?_⟩
    apply basis.repr.injective
    ext j
    change basis.repr g j = basis.repr ((c : ℂ) • f) j
    rw [map_smul]
    change basis.repr g j = phase * basis.repr f j
    have hg : basis.repr g p ≠ 0 := norm_ne_zero_iff.mp (by rw [← hn]; exact norm_ne_zero_iff.mpr hp)
    apply mul_left_cancel₀ ((map_ne_zero (starRingEnd ℂ)).mpr hg)
    have hrow := h p j
    have hdiag := h p p
    dsimp [phase]
    field_simp [hp]
    linear_combination -(basis.repr f p) * hrow + (basis.repr f j) * hdiag

end OperatorPhaseRetrieval.TwoUnitary
