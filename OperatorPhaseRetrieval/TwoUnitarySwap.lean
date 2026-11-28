module

public import OperatorPhaseRetrieval.TwoUnitaryFourier
public import Mathlib.Data.Int.ModEq

@[expose] public section

/-! A periodic permutation whose commutator with a Fourier shift agrees with a prescribed
matrix unit on an arbitrary finite window. -/
noncomputable section

open scoped InnerProductSpace

namespace OperatorPhaseRetrieval.TwoUnitary

def swapClasses (L u v x : ℤ) : ℤ :=
  if x ≡ u [ZMOD L] then x + (v-u)
  else if x ≡ v [ZMOD L] then x + (u-v) else x

theorem swapClasses_involutive {L u v : ℤ} (huv : ¬ u ≡ v [ZMOD L]) :
    Function.Involutive (swapClasses L u v) := by
  intro x
  by_cases hu : x ≡ u [ZMOD L]
  · have h : x+(v-u) ≡ v [ZMOD L] := by
      convert hu.add_right (v-u) using 1
      ring
    have hn : ¬ x+(v-u) ≡ u [ZMOD L] := fun he => huv (he.symm.trans h)
    simp only [swapClasses, ite_eq_left hu, ite_eq_right hn, ite_eq_left h]
    ring
  · by_cases hv : x ≡ v [ZMOD L]
    · have h : x+(u-v) ≡ u [ZMOD L] := by
        convert hv.add_right (u-v) using 1
        ring
      simp only [swapClasses, ite_eq_right hu, ite_eq_left hv, ite_eq_left h]
      ring
    · simp [swapClasses, hu, hv]

def swapPerm {L u v : ℤ} (huv : ¬ u ≡ v [ZMOD L]) : Equiv.Perm ℤ where
  toFun := swapClasses L u v
  invFun := swapClasses L u v
  left_inv := swapClasses_involutive huv
  right_inv := swapClasses_involutive huv

theorem swapClasses_period (L u v x : ℤ) :
    swapClasses L u v (L+x) = L + swapClasses L u v x := by
  simp only [swapClasses, Int.modulus_add_modEq_iff]
  split <;> (try split) <;> omega

theorem close_congruent {L x y : ℤ} (lo : -L < y-x) (hi : y-x < L)
    (h : x ≡ y [ZMOD L]) : x = y := by
  have he := Int.eq_zero_of_abs_lt_dvd h.dvd (abs_lt.mpr ⟨lo,hi⟩)
  omega

/-- A periodic swap isolates the (i,j) matrix entry in the Fourier window [-k,k].
The testing frequency is a positive multiple of the prescribed period d. -/
theorem exists_swap (i j : ℤ) (k d : ℕ) (hd : 0 < d) :
    ∃ (m : ℕ) (R : Op), 0 < m ∧ IsUnitary R ∧ star R = R ∧
      Commute R (shift (4 * ((m*d : ℕ) : ℤ))) ∧
      ∀ a ∈ Finset.Icc (-(k:ℤ)) k, ∀ b ∈ Finset.Icc (-(k:ℤ)) k,
        entry (shift (m*d : ℕ) * R - R * shift (m*d : ℕ)) a b =
          (if a = i ∧ b = j then 1 else 0) := by
  let B := k + i.natAbs + j.natAbs + 1
  let m := 4*B + 1
  let N : ℤ := (m*d : ℕ)
  have hk : (k : ℤ) ≤ B := by dsimp [B]; omega
  have hB (x : ℤ) (hx : x.natAbs ≤ B) : -(B:ℤ) ≤ x ∧ x ≤ B := by
    have h : |x| ≤ (B:ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hx
    exact abs_le.mp h
  have hi := hB i (by dsimp [B]; omega)
  have hj := hB j (by dsimp [B]; omega)
  have hN : 4*(B:ℤ) < N := by
    have hm := Nat.le_mul_of_pos_right m hd
    dsimp only [N]
    exact_mod_cast (show 4*B < m*d by dsimp [m] at hm ⊢; omega)
  have huv : ¬ j ≡ i-N [ZMOD 4*N] := by
    intro h
    have := close_congruent (by omega) (by omega) h
    omega
  let r := swapPerm huv
  let R := permOp r
  have huR := permOp_unitary r
  have hR : R * R = 1 := by
    apply basis_ext
    intro b
    change permOp r (permOp r (basis b)) = basis b
    rw [permOp_basis, permOp_basis]
    exact congrArg basis (swapClasses_involutive huv b)
  refine ⟨m, R, by dsimp [m]; omega, huR, ?_, ?_, ?_⟩
  · calc
      star R = star R * (R * R) := by rw [hR, mul_one]
      _ = R := by rw [← mul_assoc, huR.1, one_mul]
  · apply basis_ext
    intro b
    change permOp r (shift (4*N) (basis b)) = shift (4*N) (permOp r (basis b))
    simp only [shift_basis, permOp_basis]
    exact congrArg basis (swapClasses_period _ _ _ _)
  · intro a ha b hb
    obtain ⟨ha₁,ha₂⟩ := Finset.mem_Icc.mp ha
    obtain ⟨hb₁,hb₂⟩ := Finset.mem_Icc.mp hb
    have hbv : ¬ b ≡ i-N [ZMOD 4*N] := by
      intro h
      have := close_congruent (by omega) (by omega) h
      omega
    have hNu : ¬ N+b ≡ j [ZMOD 4*N] := by
      intro h
      have := close_congruent (by omega) (by omega) h
      omega
    have hNv : ¬ N+b ≡ i-N [ZMOD 4*N] := by
      intro h
      have := close_congruent (by omega) (by omega) h
      omega
    have hfixed : r (N+b) = N+b := by
      change swapClasses _ _ _ _ = _
      simp [swapClasses, hNu, hNv]
    change inner ℂ (basis a) (shift N (permOp r (basis b)) - permOp r (shift N (basis b))) = _
    simp only [permOp_basis, shift_basis, hfixed, inner_sub_right, orthonormal_iff_ite.mp basis.orthonormal]
    by_cases hbj : b = j
    · subst b
      have hmove : r j = i-N := by
        change swapClasses _ _ _ _ = _
        simp [swapClasses]
      rw [hmove]
      have hfar : a ≠ N+j := by omega
      simp [hfar]
    · have hbu : ¬ b ≡ j [ZMOD 4*N] := fun h =>
        hbj (close_congruent (by omega) (by omega) h)
      have hsame : r b = b := by
        change swapClasses _ _ _ _ = _
        simp [swapClasses, hbu, hbv]
      simp [hsame,hbj]

end OperatorPhaseRetrieval.TwoUnitary
