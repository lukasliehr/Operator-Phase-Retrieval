import OperatorPhaseRetrieval.TwoUnitarySwap
import OperatorPhaseRetrieval.TwoUnitaryRotation
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Algebra.Star.Unitary

/-! A common near-identity unitary for the countable family of Fourier tests. -/
noncomputable section

open Set Filter
open scoped Topology InnerProductSpace
namespace OperatorPhaseRetrieval.TwoUnitary

def periodic : Set Op :=
  {V | IsUnitary V ∧ ∃ d : ℕ, 0 < d ∧ Commute V (shift d)}

private abbrev K := ↥(closure periodic)

private instance : CompleteSpace K :=
  @IsClosed.completeSpace_coe _ _ _ _ isClosed_closure

private theorem unitary_of_mem (x : K) : IsUnitary x.val :=
  (closure_minimal (fun _ hx => hx.1) isClosed_unitary : closure periodic ⊆
    (unitary Op : Set Op)) x.property

def window (k : ℕ) := Finset.Icc (-(k : ℤ)) k

def targetEntry (i j a b : ℤ) : ℂ := if a = i ∧ b = j then 1 else 0

def fits (i j : ℤ) (k : ℕ) (A : Op) : Prop :=
  ‖A‖ < 3 ∧ ∀ a ∈ window k, ∀ b ∈ window k,
    ‖entry A a b - targetEntry i j a b‖ < 1 / ((k : ℝ) + 1)

private def good (i j : ℤ) (k : ℕ) : Set K :=
  {x | ∃ (N : ℕ) (z : ℂ), 0 < N ∧ z ≠ 0 ∧ fits i j k (readout x.val N z)}

private theorem open_fits (i j : ℤ) (k : ℕ) : IsOpen {A | fits i j k A} := by
  let box := ↥(window k)
  have he : {A : Op | fits i j k A} = {A | ‖A‖ < 3} ∩
      ⋂ (a : box) (b : box), {A | ‖entry A a b - targetEntry i j a b‖ < 1 / ((k:ℝ)+1)} := by
    ext A
    simp [fits, box]
  rw [he]
  refine (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => ?_)
  apply isOpen_lt _ continuous_const
  unfold entry
  fun_prop

private theorem open_good (i j : ℤ) (k : ℕ) : IsOpen (good i j k) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨N,z,hN,hz,hfit⟩
  have hc : Continuous (fun x : K => readout x.val N z) := by unfold readout; fun_prop
  have hs := (open_fits i j k).preimage hc
  exact Filter.mem_of_superset (hs.mem_nhds hfit) (fun y hy => ⟨N,z,hN,hz,hy⟩)

private theorem dense_good (i j : ℤ) (k : ℕ)
    (step : ∀ V ∈ periodic, ∀ r : ℝ, 0 < r →
      ∃ U ∈ periodic, ‖U - V‖ < r ∧ ∃ (N : ℕ) (z : ℂ),
        0 < N ∧ z ≠ 0 ∧ fits i j k (readout U N z)) : Dense (good i j k) := by
  intro x
  apply Metric.mem_closure_iff.mpr
  intro r hr
  obtain ⟨V,hV,hx⟩ := Metric.mem_closure_iff.mp x.property (r/2) (half_pos hr)
  obtain ⟨U,hU,hu,hgood⟩ := step V hV _ (half_pos hr)
  refine ⟨⟨U,subset_closure hU⟩, hgood, ?_⟩
  change dist (x : Op) U < r
  have := dist_triangle (x : Op) V U
  rw [dist_comm V U, dist_eq_norm U V] at this
  linarith

private theorem entry_sub_bound (A B : Op) (a b : ℤ) :
    ‖entry A a b - entry B a b‖ ≤ ‖A - B‖ := by
  calc
    _ = ‖inner ℂ (basis a) ((A-B) (basis b))‖ := by
      simp only [entry, sub_apply, inner_sub_right]
    _ ≤ ‖basis a‖ * ‖(A-B) (basis b)‖ := norm_inner_le_norm _ _
    _ ≤ ‖basis a‖ * (‖A-B‖ * ‖basis b‖) := by
      gcongr
      exact (A-B).le_opNorm _
    _ = _ := by rw [basis.orthonormal.norm_eq_one, basis.orthonormal.norm_eq_one]; ring

private theorem periodic_step (i j : ℤ) (k : ℕ) (V : Op) (hV : V ∈ periodic)
    (r : ℝ) (hr : 0 < r) :
    ∃ U ∈ periodic, ‖U - V‖ < r ∧ ∃ (N : ℕ) (z : ℂ),
      0 < N ∧ z ≠ 0 ∧ fits i j k (readout U N z) := by
  obtain ⟨hu,d,hd,hper⟩ := hV
  obtain ⟨m,R,hm,hR,hstar,hrep,hswap⟩ := exists_swap i j k d hd
  let N := m*d
  have hN : 0 < N := Nat.mul_pos hm hd
  have hc : Commute V (shift N) := by
    rw [show (N : ℤ) = (m : ℤ) * (d : ℤ) by simp [N], shift_nat_mul]
    exact hper.pow_right m
  have hc4 : Commute V (shift (4*(N : ℤ))) := by
    rw [show (4:ℤ) = ((4:ℕ):ℤ) from rfl, shift_nat_mul]
    exact hc.pow_right _
  let s := 1 / ((k : ℝ) + 1)
  have hs : 0 < s := by dsimp [s]; positivity
  let δ := min r (s/2)
  obtain ⟨W,z,hU,hperiod,hnear,hz,hn,herr⟩ := exists_step V R N (4*(N:ℤ)) δ
    (lt_min hr (half_pos hs)) hu hR hstar hc hc4 hrep
  refine ⟨V*W, ⟨hU,4*N,by positivity,by simpa using hperiod⟩,
    hnear.trans_le (min_le_left _ _), N,z,hN,hz,hn.trans_lt (by norm_num), ?_⟩
  intro a ha b hb
  rw [targetEntry, ← hswap a ha b hb]
  apply (entry_sub_bound _ _ a b).trans_lt
  exact herr.trans_le (by have := min_le_right r (s/2); dsimp only [δ]; linarith)

theorem simultaneous_readouts
    (ε : ℝ) (hε : 0 < ε) :
    ∃ V : Op, IsUnitary V ∧ ‖V - 1‖ < ε ∧ ∀ i j : ℤ,
      ∃ (N : ℕ → ℕ) (z : ℕ → ℂ), (∀ k, ‖readout V (N k) (z k)‖ ≤ 3) ∧
        ∀ a b, Tendsto (fun k => entry (readout V (N k) (z k)) a b) atTop
          (𝓝 (targetEntry i j a b)) := by
  let G (t : ℤ × ℤ × ℕ) := good t.1 t.2.1 t.2.2
  have hd : Dense (⋂ t, G t) := dense_iInter_of_isOpen
    (fun t => open_good t.1 t.2.1 t.2.2)
    (fun t => dense_good _ _ _ (periodic_step t.1 t.2.1 t.2.2))
  have hone : (1 : Op) ∈ periodic :=
    ⟨⟨by simp, by simp⟩, 1, by decide, Commute.one_left _⟩
  let origin : K := ⟨1,subset_closure hone⟩
  obtain ⟨V,hV,hnear⟩ := Metric.mem_closure_iff.mp (hd origin) ε hε
  refine ⟨V.val, unitary_of_mem V, ?_, ?_⟩
  · simpa only [dist_comm origin V, Subtype.dist_eq, dist_eq_norm] using hnear
  intro i j
  have h (k : ℕ) := Set.mem_iInter.mp hV (i,j,k)
  change ∀ k : ℕ, ∃ (N : ℕ) (z : ℂ), 0 < N ∧ z ≠ 0 ∧ fits i j k (readout V.val N z) at h
  choose N z _ _ hb using h
  refine ⟨N,z,fun k => (hb k).1.le, fun a b => ?_⟩
  apply Metric.tendsto_atTop.mpr
  intro δ hδ
  obtain ⟨m,hm⟩ := Metric.tendsto_atTop.mp
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) δ hδ
  refine ⟨max m (max a.natAbs b.natAbs), fun k hk => ?_⟩
  have memBox (c : ℤ) (hc : c.natAbs ≤ k) : c ∈ window k := by
    simp only [window, Finset.mem_Icc]
    omega
  have hsmall := hm k (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hsmall
  rw [dist_eq_norm]
  exact ((hb k).2 a (memBox a (by omega)) b (memBox b (by omega))).trans hsmall

end OperatorPhaseRetrieval.TwoUnitary
