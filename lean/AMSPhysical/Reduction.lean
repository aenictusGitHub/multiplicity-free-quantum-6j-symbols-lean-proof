import Radial

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section

namespace AMSPhysical
open MvPolynomial
variable {R : Type*} [CommRing R]

@[simp] theorem pull_X (i : Fin 4) : pull (X i : P4 R)=coords i := by simp [pull]
@[simp] theorem pull_natCast (n : ℕ) : pull (n : P4 R)=(n:P8 R) := map_natCast _ n

theorem dx0_pull (p : P4 R) :
    pderiv 0 (pull p)=X 4*pull (pderiv 0 p)+X 6*pull (pderiv 1 p) := by
  rw [pd_pull]
  simp [Fin.sum_univ_succ,coords]

theorem dx1_pull (p : P4 R) :
    pderiv 1 (pull p)=X 5*pull (pderiv 0 p)+X 7*pull (pderiv 1 p) := by
  rw [pd_pull]
  simp [Fin.sum_univ_succ,coords]

theorem dz0_pull (p : P4 R) :
    pderiv 2 (pull p)=X 4*pull (pderiv 2 p)+X 6*pull (pderiv 3 p) := by
  rw [pd_pull]
  simp [Fin.sum_univ_succ,coords]

theorem dz1_pull (p : P4 R) :
    pderiv 3 (pull p)=X 5*pull (pderiv 2 p)+X 7*pull (pderiv 3 p) := by
  rw [pd_pull]
  simp [Fin.sum_univ_succ,coords]

theorem dy0_pull (p : P4 R) :
    pderiv 4 (pull p)=X 0*pull (pderiv 0 p)+X 2*pull (pderiv 2 p) := by
  rw [pd_pull]
  simp [Fin.sum_univ_succ,coords]

theorem dy1_pull (p : P4 R) :
    pderiv 5 (pull p)=X 1*pull (pderiv 0 p)+X 3*pull (pderiv 2 p) := by
  rw [pd_pull]
  simp [Fin.sum_univ_succ,coords]

theorem lap_xy_pull (p : P4 R) :
    lap 0 1 4 5 (pull p)=pull (radialXY 2 p) := by
  simp only [lap,dx0_pull,dx1_pull,map_add,pderiv_mul,dy0_pull,dy1_pull]
  simp [radialXY,coords,map_ofNat,pd_comm (2:Fin 4) 0,pd_comm (2:Fin 4) 1]
  ring

theorem lap_zy_pull (p : P4 R) :
    lap 2 3 4 5 (pull p)=pull (radialZY 2 p) := by
  simp only [lap,dz0_pull,dz1_pull,map_add,pderiv_mul,dy0_pull,dy1_pull]
  simp [radialZY,coords,map_ofNat]
  ring

def shiftI (h : ℕ) (p : P4 R) : P8 R := detY^h*pull p
def shiftII (h : ℕ) (p : P4 R) : P8 R := detX^h*pull p

/-- Balanced determinant generators reduce to a polynomial in contractions.
This is the algebraic reduction used after an invariant-generating theorem. -/
theorem balanced_generator_typeI (h r : ℕ) (p : P4 R) :
    detX^r*detY^(r+h)*pull p =
      shiftI h ((X 0*X 3-X 1*X 2)^r*p) := by
  have hd : pull (X 0*X 3-X 1*X 2 : P4 R)=detX*detY := by
    simp only [map_sub,map_mul,pull_X]
    exact determinant_relation.symm
  unfold shiftI
  rw [map_mul,map_pow,hd,mul_pow,pow_add]
  ring

theorem balanced_generator_typeII (h r : ℕ) (p : P4 R) :
    detX^(r+h)*detY^r*pull p =
      shiftII h ((X 0*X 3-X 1*X 2)^r*p) := by
  have hd : pull (X 0*X 3-X 1*X 2 : P4 R)=detX*detY := by
    simp only [map_sub,map_mul,pull_X]
    exact determinant_relation.symm
  unfold shiftII
  rw [map_mul,map_pow,hd,mul_pow,pow_add]
  ring

/-- Actual Laplacian intertwining, uniformly for all ranks h+2 and all polynomials. -/
theorem typeI_lap_xy (h : ℕ) (p : P4 R) :
    lap 0 1 4 5 (shiftI h p)=shiftI h (radialXY (h+2) p) := by
  simp only [shiftI,dy_power_lap_xy,lap_xy_pull]
  rw [Nat.add_comm h 2,radialXY_rank_shift]
  simp

theorem typeI_lap_zy (h : ℕ) (p : P4 R) :
    lap 2 3 4 5 (shiftI h p)=shiftI h (radialZY (h+2) p) := by
  simp only [shiftI,dy_power_lap_zy,lap_zy_pull]
  rw [Nat.add_comm h 2,radialZY_rank_shift]
  simp

theorem typeII_lap_zy (h : ℕ) (p : P4 R) :
    lap 2 3 4 5 (shiftII h p)=shiftII h (radialZY (h+2) p) := by
  simp only [shiftII,dx_power_lap_zy,lap_zy_pull]
  rw [Nat.add_comm h 2,radialZY_rank_shift]
  simp

def sourceRaise (p : P4 R) : P4 R := X 0*pderiv 2 p+X 1*pderiv 3 p
def sourceLower (p : P4 R) : P4 R := X 2*pderiv 0 p+X 3*pderiv 1 p
def sourceEulerX (p : P4 R) : P4 R := X 0*pderiv 0 p+X 1*pderiv 1 p
def sourceOmegaXX (p : P4 R) : P4 R := sourceRaise (sourceLower p)-sourceEulerX p

theorem raise_pull (p : P4 R) : raiseColor (pull p)=pull (sourceRaise p) := by
  unfold raiseColor
  rw [dz0_pull,dz1_pull]
  simp [sourceRaise,coords]
  ring

theorem lower_pull (p : P4 R) : lowerColor (pull p)=pull (sourceLower p) := by
  unfold lowerColor
  rw [dx0_pull,dx1_pull]
  simp [sourceLower,coords]
  ring

theorem euler_pull (p : P4 R) : eulerX (pull p)=pull (sourceEulerX p) := by
  unfold eulerX
  rw [dx0_pull,dx1_pull]
  simp [sourceEulerX,coords]
  ring

theorem omega_pull (p : P4 R) : omegaXX (pull p)=pull (sourceOmegaXX p) := by
  simp only [omegaXX,sourceOmegaXX,lower_pull,raise_pull,euler_pull,map_sub]

/-- Type-II same-orientation Casimir shift, with its scalar correction. -/
theorem typeII_same_casimir (h : ℕ) (p : P4 R) :
    omegaXX (shiftII h p)=shiftII h (sourceOmegaXX p)-(h:P8 R)*shiftII h p := by
  simp only [shiftII,same_orientation_shift,omega_pull]

def mixedXYAmbient (p : P8 R) : P8 R := coords 0*lap 0 1 4 5 p
def mixedZYAmbient (p : P8 R) : P8 R := coords 2*lap 2 3 4 5 p
def mixedXYSource (n : ℕ) (p : P4 R) : P4 R := X 0*radialXY n p
def mixedZYSource (n : ℕ) (p : P4 R) : P4 R := X 2*radialZY n p

theorem typeI_pair12 (h : ℕ) (p : P4 R) :
    mixedXYAmbient (shiftI h p)=shiftI h (mixedXYSource (h+2) p) := by
  unfold mixedXYAmbient
  rw [typeI_lap_xy]
  unfold shiftI mixedXYSource
  rw [map_mul,pull_X]
  ring

theorem typeI_pair23 (h : ℕ) (p : P4 R) :
    mixedZYAmbient (shiftI h p)=shiftI h (mixedZYSource (h+2) p) := by
  unfold mixedZYAmbient
  rw [typeI_lap_zy]
  unfold shiftI mixedZYSource
  rw [map_mul,pull_X]
  ring

theorem typeII_pair23 (h : ℕ) (p : P4 R) :
    mixedZYAmbient (shiftII h p)=shiftII h (mixedZYSource (h+2) p) := by
  unfold mixedZYAmbient
  rw [typeII_lap_zy]
  unfold shiftII mixedZYSource
  rw [map_mul,pull_X]
  ring

end AMSPhysical

#print axioms AMSPhysical.typeI_pair12
#print axioms AMSPhysical.typeI_pair23
#print axioms AMSPhysical.typeII_pair23
#print axioms AMSPhysical.typeII_same_casimir
