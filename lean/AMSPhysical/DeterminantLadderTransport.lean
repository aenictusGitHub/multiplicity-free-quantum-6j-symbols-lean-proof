import PairingLadderOperators
import DeterminantFockNorm

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
open MvPolynomial

theorem lap_power_covariant (a b c d : Fin 8) (D p r : P8 ℂ)
    (ha : pderiv a D=0) (hb : pderiv b D=0)
    (hcross : pderiv c D*pderiv a p+pderiv d D*pderiv b p=D*r) (h : ℕ) :
    lap a b c d (D^h*p)=D^h*(lap a b c d p+(h:P8 ℂ)*r) := by
  cases h with
  | zero => simp
  | succ h =>
    rw [lap_mul_pow a b c d D p ha hb,hcross]
    simp only [Nat.succ_sub_one,pow_succ]
    ring

/-- All eight literal determinant/Laplacian intertwining identities, with
arbitrary determinant power and arbitrary polynomial in the four pairings. -/
theorem determinantLaplacian_transport (vectorSide : Bool) (i : Fin 4) (h : ℕ) (p : P4 ℂ) :
    pairingLaplacian8 i (determinantVacuum vectorSide^h*pull p)=
      determinantVacuum vectorSide^h*(pairingLaplacian8 i (pull p)+(h:P8 ℂ)*pull (pderiv i p)) := by
  cases vectorSide <;> fin_cases i
  · change lap 0 1 4 5 (detY^h*pull p)=detY^h*(lap 0 1 4 5 (pull p)+(h:P8 ℂ)*pull (pderiv 0 p))
    apply lap_power_covariant 0 1 4 5
    · simp [detY]
    · simp [detY]
    · simp [detY,pd_pull,Fin.sum_univ_succ,coords]
      ring
  · change lap 0 1 6 7 (detY^h*pull p)=detY^h*(lap 0 1 6 7 (pull p)+(h:P8 ℂ)*pull (pderiv 1 p))
    apply lap_power_covariant 0 1 6 7
    · simp [detY]
    · simp [detY]
    · simp [detY,pd_pull,Fin.sum_univ_succ,coords]
      ring
  · change lap 2 3 4 5 (detY^h*pull p)=detY^h*(lap 2 3 4 5 (pull p)+(h:P8 ℂ)*pull (pderiv 2 p))
    apply lap_power_covariant 2 3 4 5
    · simp [detY]
    · simp [detY]
    · simp [detY,pd_pull,Fin.sum_univ_succ,coords]
      ring
  · change lap 2 3 6 7 (detY^h*pull p)=detY^h*(lap 2 3 6 7 (pull p)+(h:P8 ℂ)*pull (pderiv 3 p))
    apply lap_power_covariant 2 3 6 7
    · simp [detY]
    · simp [detY]
    · simp [detY,pd_pull,Fin.sum_univ_succ,coords]
      ring
  · change lap 0 1 4 5 (detX^h*pull p)=detX^h*(lap 0 1 4 5 (pull p)+(h:P8 ℂ)*pull (pderiv 0 p))
    rw [lap_swap 0 1 4 5,lap_swap 0 1 4 5]
    apply lap_power_covariant 4 5 0 1
    · simp [detX]
    · simp [detX]
    · simp [detX,pd_pull,Fin.sum_univ_succ,coords]
      ring
  · change lap 0 1 6 7 (detX^h*pull p)=detX^h*(lap 0 1 6 7 (pull p)+(h:P8 ℂ)*pull (pderiv 1 p))
    rw [lap_swap 0 1 6 7,lap_swap 0 1 6 7]
    apply lap_power_covariant 6 7 0 1
    · simp [detX]
    · simp [detX]
    · simp [detX,pd_pull,Fin.sum_univ_succ,coords]
      ring
  · change lap 2 3 4 5 (detX^h*pull p)=detX^h*(lap 2 3 4 5 (pull p)+(h:P8 ℂ)*pull (pderiv 2 p))
    rw [lap_swap 2 3 4 5,lap_swap 2 3 4 5]
    apply lap_power_covariant 4 5 2 3
    · simp [detX]
    · simp [detX]
    · simp [detX,pd_pull,Fin.sum_univ_succ,coords]
      ring
  · change lap 2 3 6 7 (detX^h*pull p)=detX^h*(lap 2 3 6 7 (pull p)+(h:P8 ℂ)*pull (pderiv 3 p))
    rw [lap_swap 2 3 6 7,lap_swap 2 3 6 7]
    apply lap_power_covariant 6 7 2 3
    · simp [detX]
    · simp [detX]
    · simp [detX,pd_pull,Fin.sum_univ_succ,coords]
      ring

def determinantPairingEval (vectorSide : Bool) (h : ℕ) : P4 ℂ →ₗ[ℂ] P8 ℂ where
  toFun p := determinantVacuum vectorSide^h*pull p
  map_add' p q := by rw [map_add,mul_add]
  map_smul' a p := by rw [map_smul,mul_smul_comm];rfl

theorem determinantPairingEval_creation (vectorSide : Bool) (h : ℕ) (i : Fin 4) (p : P4 ℂ) :
    determinantPairingEval vectorSide h (X i*p)=coords i*determinantPairingEval vectorSide h p := by
  change determinantVacuum vectorSide^h*pull (X i*p)=_
  rw [map_mul,pull_X]
  change _=coords i*(determinantVacuum vectorSide^h*pull p)
  ring

theorem determinantPairingEval_annihilation (vectorSide : Bool) (h : ℕ) (i : Fin 4) (p : P4 ℂ) :
    pairingLaplacian8 i (determinantPairingEval vectorSide h p)=
      determinantPairingEval vectorSide h (pairingRadial (2+h) i p) := by
  change pairingLaplacian8 i (determinantVacuum vectorSide^h*pull p)=_
  rw [determinantLaplacian_transport,pairingLaplacian8_pull,pairingRadial_rank_shift]
  change _=determinantVacuum vectorSide^h*pull (pairingRadial 2 i p+(h:P4 ℂ)*pderiv i p)
  simp

end AMSPhysical
#print axioms AMSPhysical.determinantPairingEval_annihilation
