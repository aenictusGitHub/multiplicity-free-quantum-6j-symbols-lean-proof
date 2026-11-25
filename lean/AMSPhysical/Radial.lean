import Determinant

set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section
namespace AMSPhysical
open MvPolynomial

variable {R : Type*} [CommRing R]

/-- Four variable families of arbitrary vector-space dimension. -/
abbrev PN (R : Type*) [CommRing R] (n : ℕ) := MvPolynomial (Fin 4 × Fin n) R

def dotN (n : ℕ) (a b : Fin 4) : PN R n := ∑ i, X (a,i)*X (b,i)

def coordsN (n : ℕ) : Fin 4 → PN R n :=
  ![dotN n 0 2, dotN n 0 3, dotN n 1 2, dotN n 1 3]

def pullN (n : ℕ) : P4 R →ₐ[R] PN R n := aeval (coordsN n)

theorem pd_dotN (n : ℕ) (a b v : Fin 4) (i : Fin n) :
    pderiv (v,i) (dotN (R:=R) n a b) =
      (if v=a then X (b,i) else 0) + (if v=b then X (a,i) else 0) := by
  classical
  by_cases hva : v=a <;> by_cases hvb : v=b <;>
    simp_all [dotN, pderiv_mul, pderiv_X, Pi.single_apply,
      Prod.mk.injEq, Finset.sum_add_distrib, mul_ite, ite_mul,
      eq_comm, add_comm]

theorem pd_pullN (n : ℕ) (v : Fin 4 × Fin n) (p : P4 R) :
    pderiv v (pullN n p) =
      ∑ k : Fin 4, pderiv v (coordsN n k) * pullN n (pderiv k p) :=
  deriv_aeval (pderiv v) (coordsN n) p

theorem dx_pullN (n : ℕ) (i : Fin n) (p : P4 R) :
    pderiv (0,i) (pullN n p) = X (2,i)*pullN n (pderiv 0 p) +
      X (3,i)*pullN n (pderiv 1 p) := by
  rw [pd_pullN]
  simp [Fin.sum_univ_succ, coordsN, pd_dotN]

theorem dz_pullN (n : ℕ) (i : Fin n) (p : P4 R) :
    pderiv (1,i) (pullN n p) = X (2,i)*pullN n (pderiv 2 p) +
      X (3,i)*pullN n (pderiv 3 p) := by
  rw [pd_pullN]
  simp [Fin.sum_univ_succ, coordsN, pd_dotN]

theorem dy_pullN (n : ℕ) (i : Fin n) (p : P4 R) :
    pderiv (2,i) (pullN n p) = X (0,i)*pullN n (pderiv 0 p) +
      X (1,i)*pullN n (pderiv 2 p) := by
  rw [pd_pullN]
  simp [Fin.sum_univ_succ, coordsN, pd_dotN]

def lapN (n : ℕ) (v w : Fin 4) (p : PN R n) : PN R n :=
  ∑ i, pderiv (w,i) (pderiv (v,i) p)

def radialXY (n : ℕ) (p : P4 R) : P4 R :=
  (n:P4 R)*pderiv 0 p +
  X 0*pderiv 0 (pderiv 0 p) + X 1*pderiv 0 (pderiv 1 p) +
  X 2*pderiv 0 (pderiv 2 p) + X 3*pderiv 1 (pderiv 2 p)

def radialZY (n : ℕ) (p : P4 R) : P4 R :=
  (n:P4 R)*pderiv 2 p +
  X 0*pderiv 0 (pderiv 2 p) + X 1*pderiv 0 (pderiv 3 p) +
  X 2*pderiv 2 (pderiv 2 p) + X 3*pderiv 2 (pderiv 3 p)

theorem radialXY_rank_shift (n h : ℕ) (p : P4 R) :
    radialXY (n+h) p = radialXY n p+(h:P4 R)*pderiv 0 p := by
  simp only [radialXY,Nat.cast_add]
  ring

theorem radialZY_rank_shift (n h : ℕ) (p : P4 R) :
    radialZY (n+h) p = radialZY n p+(h:P4 R)*pderiv 2 p := by
  simp only [radialZY,Nat.cast_add]
  ring

/-- The radial part is derived from actual ambient polynomial derivatives. -/
theorem radialXY_actual (n : ℕ) (p : P4 R) :
    lapN n 0 2 (pullN n p) = pullN n (radialXY n p) := by
  classical
  simp only [lapN, dx_pullN, map_add, pderiv_mul, dy_pullN, pderiv_X]
  simp only [Pi.single_apply, Prod.mk.injEq]
  simp only [true_and, false_and, ite_true, ite_false, one_mul, zero_mul, zero_add,
    add_zero, mul_add, Finset.sum_add_distrib]
  simp only [← mul_assoc, ← Finset.sum_mul]
  simp [radialXY, pullN, coordsN, dotN, Finset.sum_mul, Finset.mul_sum,
    pd_comm (2:Fin 4) 0, pd_comm (2:Fin 4) 1, mul_comm, mul_left_comm, mul_assoc]
  ring

theorem radialZY_actual (n : ℕ) (p : P4 R) :
    lapN n 1 2 (pullN n p) = pullN n (radialZY n p) := by
  classical
  simp only [lapN, dz_pullN, map_add, pderiv_mul, dy_pullN, pderiv_X]
  simp only [Pi.single_apply, Prod.mk.injEq]
  simp only [true_and, false_and, ite_true, ite_false, one_mul, zero_mul, zero_add,
    add_zero, mul_add, Finset.sum_add_distrib]
  simp only [← mul_assoc, ← Finset.sum_mul]
  simp [radialZY, pullN, coordsN, dotN, Finset.sum_mul, Finset.mul_sum,
    mul_comm, mul_left_comm, mul_assoc]
  ring

end AMSPhysical

#print axioms AMSPhysical.radialXY_actual
#print axioms AMSPhysical.radialZY_actual
