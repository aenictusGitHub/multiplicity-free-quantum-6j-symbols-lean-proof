import FockEight
import PolynomialAdjointGram

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
open MvPolynomial
variable {R : Type*} [CommRing R]

def radialXW (n : ℕ) (p : P4 R) : P4 R :=
  (n:P4 R)*pderiv 1 p+
  X 0*pderiv 0 (pderiv 1 p)+X 1*pderiv 1 (pderiv 1 p)+
  X 2*pderiv 0 (pderiv 3 p)+X 3*pderiv 1 (pderiv 3 p)

def radialZW (n : ℕ) (p : P4 R) : P4 R :=
  (n:P4 R)*pderiv 3 p+
  X 0*pderiv 1 (pderiv 2 p)+X 1*pderiv 1 (pderiv 3 p)+
  X 2*pderiv 2 (pderiv 3 p)+X 3*pderiv 3 (pderiv 3 p)

def pairingRadial (n : ℕ) (i : Fin 4) (p : P4 R) : P4 R :=
  ![radialXY n p,radialXW n p,radialZY n p,radialZW n p] i

def pairingVectorSlot (i : Fin 4) : Fin 4 := ![0,0,1,1] i
def pairingCovectorSlot (i : Fin 4) : Fin 4 := ![2,3,2,3] i

def pairingLaplacian8 (i : Fin 4) (p : P8 R) : P8 R :=
  ![lap 0 1 4 5 p,lap 0 1 6 7 p,lap 2 3 4 5 p,lap 2 3 6 7 p] i

theorem pairing_dw_pullN (n : ℕ) (i : Fin n) (p : P4 R) :
    pderiv (3,i) (pullN n p)=X (0,i)*pullN n (pderiv 1 p)+X (1,i)*pullN n (pderiv 3 p) := by
  rw [pd_pullN]
  simp [Fin.sum_univ_succ,coordsN,pd_dotN]

theorem radialXW_actual (n : ℕ) (p : P4 R) :
    lapN n 0 3 (pullN n p)=pullN n (radialXW n p) := by
  classical
  simp only [lapN,dx_pullN,map_add,pderiv_mul,pairing_dw_pullN,pderiv_X]
  simp only [Pi.single_apply,Prod.mk.injEq,true_and,false_and,ite_true,ite_false,
    one_mul,zero_mul,zero_add,add_zero,mul_add,Finset.sum_add_distrib]
  simp only [← mul_assoc,← Finset.sum_mul]
  simp [radialXW,pullN,coordsN,dotN,Finset.sum_mul,Finset.mul_sum,
    pd_comm (3:Fin 4) 0,pd_comm (3:Fin 4) 1,pd_comm (1:Fin 4) 0,mul_comm,mul_left_comm,mul_assoc]
  ring

theorem radialZW_actual (n : ℕ) (p : P4 R) :
    lapN n 1 3 (pullN n p)=pullN n (radialZW n p) := by
  classical
  simp only [lapN,dz_pullN,map_add,pderiv_mul,pairing_dw_pullN,pderiv_X]
  simp only [Pi.single_apply,Prod.mk.injEq,true_and,false_and,ite_true,ite_false,
    one_mul,zero_mul,zero_add,add_zero,mul_add,Finset.sum_add_distrib]
  simp only [← mul_assoc,← Finset.sum_mul]
  simp [radialZW,pullN,coordsN,dotN,Finset.sum_mul,Finset.mul_sum,
    pd_comm (3:Fin 4) 2,mul_comm,mul_left_comm,mul_assoc]
  ring

theorem pairingRadial_actual (n : ℕ) (i : Fin 4) (p : P4 R) :
    lapN n (pairingVectorSlot i) (pairingCovectorSlot i) (pullN n p)=pullN n (pairingRadial n i p) := by
  fin_cases i
  · exact radialXY_actual n p
  · exact radialXW_actual n p
  · exact radialZY_actual n p
  · exact radialZW_actual n p

theorem pairingRadial_one (n : ℕ) (i : Fin 4) : pairingRadial (R:=R) n i 1=0 := by
  fin_cases i <;> simp [pairingRadial,radialXY,radialXW,radialZY,radialZW]

theorem pairingRadial_rank_shift (n h : ℕ) (i : Fin 4) (p : P4 R) :
    pairingRadial (n+h) i p=pairingRadial n i p+(h:P4 R)*pderiv i p := by
  fin_cases i <;> simp [pairingRadial,radialXY,radialXW,radialZY,radialZW,Nat.cast_add] <;> ring

theorem pairing_dw0_pull (p : P4 R) :
    pderiv 6 (pull p)=X 0*pull (pderiv 1 p)+X 2*pull (pderiv 3 p) := by
  rw [pd_pull]
  simp [Fin.sum_univ_succ,coords]

theorem pairing_dw1_pull (p : P4 R) :
    pderiv 7 (pull p)=X 1*pull (pderiv 1 p)+X 3*pull (pderiv 3 p) := by
  rw [pd_pull]
  simp [Fin.sum_univ_succ,coords]

theorem lap_xw_pull (p : P4 R) : lap 0 1 6 7 (pull p)=pull (radialXW 2 p) := by
  simp only [lap,dx0_pull,dx1_pull,map_add,pderiv_mul,pairing_dw0_pull,pairing_dw1_pull]
  simp [radialXW,coords,map_ofNat,pd_comm (3:Fin 4) 0,pd_comm (3:Fin 4) 1,pd_comm (1:Fin 4) 0]
  ring

theorem lap_zw_pull (p : P4 R) : lap 2 3 6 7 (pull p)=pull (radialZW 2 p) := by
  simp only [lap,dz0_pull,dz1_pull,map_add,pderiv_mul,pairing_dw0_pull,pairing_dw1_pull]
  simp [radialZW,coords,map_ofNat,pd_comm (3:Fin 4) 2]
  ring

theorem pairingLaplacian8_pull (i : Fin 4) (p : P4 R) :
    pairingLaplacian8 i (pull p)=pull (pairingRadial 2 i p) := by
  fin_cases i
  · exact lap_xy_pull p
  · exact lap_xw_pull p
  · exact lap_zy_pull p
  · exact lap_zw_pull p

theorem pairingLaplacian8_adjoint (i : Fin 4) (p q : P8 ℂ) :
    fock (coords i*p) q=fock p (pairingLaplacian8 i q) := by
  fin_cases i <;>
    simp [coords,pairingLaplacian8,lap,add_mul,fock_add_left,fock_add_right,
      mul_assoc,fock_mulX_pderiv]

theorem pairingRadial_fock_adjoint (n : ℕ) (i : Fin 4) (p q : P4 ℂ) :
    fock (pullN n (X i*p)) (pullN n q)=fock (pullN n p) (pullN n (pairingRadial n i q)) := by
  rw [map_mul]
  have hc : pullN (R:=ℂ) n (X i)=dotN n (pairingVectorSlot i) (pairingCovectorSlot i) := by
    fin_cases i <;> simp [pullN,coordsN,pairingVectorSlot,pairingCovectorSlot]
  rw [hc,fock_contraction_lap,pairingRadial_actual]

end AMSPhysical
#print axioms AMSPhysical.pairingRadial_actual
#print axioms AMSPhysical.pairingRadial_fock_adjoint
