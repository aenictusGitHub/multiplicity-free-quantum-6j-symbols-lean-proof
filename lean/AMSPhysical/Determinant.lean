import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section

namespace AMSPhysical
open MvPolynomial

variable {R : Type*} [CommRing R]

/-- Formal chain rule for evaluation of a multivariate polynomial. -/
theorem deriv_aeval {S σ : Type*} [CommRing S] [Algebra R S]
    [Fintype σ] [DecidableEq σ] (D : Derivation R S S)
    (z : σ → S) (p : MvPolynomial σ R) :
    D (aeval z p) = ∑ i, D (z i) * aeval z (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq =>
    simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp only [map_mul, aeval_X, pderiv_mul, pderiv_X, map_add, mul_add,
      Finset.sum_add_distrib]
    simp only [← mul_assoc, ← Finset.sum_mul]
    simp [Derivation.leibniz, hp, Pi.single_apply, ite_mul, mul_comm]

abbrev P8 (R : Type*) [CommRing R] := MvPolynomial (Fin 8) R
abbrev P4 (R : Type*) [CommRing R] := MvPolynomial (Fin 4) R

def coords : Fin 4 → P8 R := ![
  X 0 * X 4 + X 1 * X 5,
  X 0 * X 6 + X 1 * X 7,
  X 2 * X 4 + X 3 * X 5,
  X 2 * X 6 + X 3 * X 7]

def pull : P4 R →ₐ[R] P8 R := aeval coords

def detX : P8 R := X 0 * X 3 - X 1 * X 2
def detY : P8 R := X 4 * X 7 - X 5 * X 6

theorem determinant_relation :
    (detX : P8 R) * detY = coords 0 * coords 3 - coords 1 * coords 2 := by
  simp [detX, detY, coords]
  ring

theorem pd_pull (i : Fin 8) (p : P4 R) :
    pderiv i (pull p) = ∑ k : Fin 4, pderiv i (coords k) * pull (pderiv k p) :=
  deriv_aeval (pderiv i) coords p

theorem cross_detY_x (p : P4 R) :
    X 7 * pderiv 0 (pull p) - X 6 * pderiv 1 (pull p) =
      detY * pull (pderiv 0 p) := by
  rw [pd_pull, pd_pull]
  simp [Fin.sum_univ_succ, coords, pderiv_mul, detY]
  ring

theorem cross_detY_z (p : P4 R) :
    X 7 * pderiv 2 (pull p) - X 6 * pderiv 3 (pull p) =
      detY * pull (pderiv 2 p) := by
  rw [pd_pull, pd_pull]
  simp [Fin.sum_univ_succ, coords, pderiv_mul, detY]
  ring

theorem cross_detX_y (p : P4 R) :
    -(X 1 * pderiv 4 (pull p)) + X 0 * pderiv 5 (pull p) =
      detX * pull (pderiv 2 p) := by
  rw [pd_pull, pd_pull]
  simp [Fin.sum_univ_succ, coords, pderiv_mul, detX]
  ring

theorem pd_comm {σ : Type*} [DecidableEq σ] (i j : σ) (p : MvPolynomial σ R) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp =>
    simp only [pderiv_mul, map_add, pderiv_X]
    by_cases hi : k=i <;> by_cases hj : k=j <;>
      simp_all [Pi.single_apply, apply_ite]

def lap (x₁ x₂ y₁ y₂ : Fin 8) (p : P8 R) : P8 R :=
  pderiv y₁ (pderiv x₁ p) + pderiv y₂ (pderiv x₂ p)

theorem lap_swap (x₁ x₂ y₁ y₂ : Fin 8) (p : P8 R) :
    lap x₁ x₂ y₁ y₂ p = lap y₁ y₂ x₁ x₂ p := by
  simp only [lap, pd_comm y₁ x₁, pd_comm y₂ x₂]

theorem lap_mul_pow (x₁ x₂ y₁ y₂ : Fin 8) (D p : P8 R)
    (hx₁ : pderiv x₁ D=0) (hx₂ : pderiv x₂ D=0) (h : ℕ) :
    lap x₁ x₂ y₁ y₂ (D^h*p) = D^h*lap x₁ x₂ y₁ y₂ p +
      (h : P8 R)*D^(h-1)*(pderiv y₁ D*pderiv x₁ p +
        pderiv y₂ D*pderiv x₂ p) := by
  simp [lap, pderiv_mul, pderiv_pow, hx₁, hx₂]
  ring

theorem dy_power_lap_xy (h : ℕ) (p : P4 R) :
    lap 0 1 4 5 (detY^h * pull p) =
      detY^h * (lap 0 1 4 5 (pull p) + (h : P8 R)*pull (pderiv 0 p)) := by
  cases h with
  | zero => simp
  | succ h =>
    rw [lap_mul_pow]
    · have he := cross_detY_x p
      have hcross : pderiv 4 detY * pderiv 0 (pull p) +
          pderiv 5 detY * pderiv 1 (pull p) = detY * pull (pderiv 0 p) := by
        simpa [detY, sub_eq_add_neg] using he
      rw [hcross]
      simp only [Nat.succ_sub_one, pow_succ]
      ring
    · simp [detY, pderiv_mul]
    · simp [detY, pderiv_mul]

theorem dy_power_lap_zy (h : ℕ) (p : P4 R) :
    lap 2 3 4 5 (detY^h * pull p) =
      detY^h * (lap 2 3 4 5 (pull p) + (h : P8 R)*pull (pderiv 2 p)) := by
  cases h with
  | zero => simp
  | succ h =>
    rw [lap_mul_pow]
    · have hcross : pderiv 4 detY * pderiv 2 (pull p) +
          pderiv 5 detY * pderiv 3 (pull p) = detY * pull (pderiv 2 p) := by
        simpa [detY, sub_eq_add_neg] using cross_detY_z p
      rw [hcross]
      simp only [Nat.succ_sub_one, pow_succ]
      ring
    · simp [detY]
    · simp [detY]

theorem dx_power_lap_zy (h : ℕ) (p : P4 R) :
    lap 2 3 4 5 (detX^h * pull p) =
      detX^h * (lap 2 3 4 5 (pull p) + (h : P8 R)*pull (pderiv 2 p)) := by
  rw [lap_swap 2 3 4 5, lap_swap 2 3 4 5]
  cases h with
  | zero => simp
  | succ h =>
    rw [lap_mul_pow]
    · have hcross : pderiv 2 detX * pderiv 4 (pull p) +
          pderiv 3 detX * pderiv 5 (pull p) = detX * pull (pderiv 2 p) := by
        simpa [detX, sub_eq_add_neg] using cross_detX_y p
      rw [hcross]
      simp only [Nat.succ_sub_one, pow_succ]
      ring
    · simp [detX]
    · simp [detX]

def raiseColor (p : P8 R) : P8 R := X 0*pderiv 2 p + X 1*pderiv 3 p
def lowerColor (p : P8 R) : P8 R := X 2*pderiv 0 p + X 3*pderiv 1 p
def eulerX (p : P8 R) : P8 R := X 0*pderiv 0 p + X 1*pderiv 1 p
def omegaXX (p : P8 R) : P8 R := raiseColor (lowerColor p) - eulerX p

theorem color_raise_detX_pow (h : ℕ) (p : P8 R) :
    raiseColor (detX^h*p) = detX^h*raiseColor p := by
  simp [raiseColor, detX, pderiv_pow]
  ring

theorem color_lower_detX_pow (h : ℕ) (p : P8 R) :
    lowerColor (detX^h*p) = detX^h*lowerColor p := by
  simp [lowerColor, detX, pderiv_pow]
  ring

theorem euler_detX_pow (h : ℕ) (p : P8 R) :
    eulerX (detX^h*p) = detX^h*(eulerX p+(h:P8 R)*p) := by
  cases h with
  | zero => simp [eulerX]
  | succ h =>
    simp only [eulerX, pderiv_mul, pderiv_pow, Nat.succ_sub_one]
    have hd0 : pderiv 0 (detX : P8 R) = X 3 := by simp [detX]
    have hd1 : pderiv 1 (detX : P8 R) = -X 2 := by simp [detX]
    rw [hd0, hd1]
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    unfold detX
    ring

theorem same_orientation_shift (h : ℕ) (p : P8 R) :
    omegaXX (detX^h*p) = detX^h*omegaXX p-(h:P8 R)*(detX^h*p) := by
  simp only [omegaXX, color_lower_detX_pow, color_raise_detX_pow, euler_detX_pow]
  ring

/-- Set x=(1,0), z=(0,1), leaving the four contractions independent. -/
def evalBack : P8 R →ₐ[R] P4 R := aeval ![1,0,0,1,X 0,X 2,X 1,X 3]

theorem evalBack_pull (p : P4 R) : evalBack (pull p) = p := by
  have he : (evalBack : P8 R →ₐ[R] P4 R).comp pull = AlgHom.id R (P4 R) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [evalBack,pull,coords]
  exact DFunLike.congr_fun he p

theorem pull_injective : Function.Injective (pull : P4 R → P8 R) :=
  Function.LeftInverse.injective evalBack_pull

theorem detY_ne_zero [Nontrivial R] : (detY : P8 R) ≠ 0 := by
  let v : Fin 8 → R := ![0,0,0,0,1,0,0,1]
  have he : MvPolynomial.eval v (detY : P8 R) = 1 := by simp [detY,v]
  intro hz
  rw [hz,map_zero] at he
  exact zero_ne_one he

theorem detX_ne_zero [Nontrivial R] : (detX : P8 R) ≠ 0 := by
  let v : Fin 8 → R := ![1,0,0,1,0,0,0,0]
  have he : MvPolynomial.eval v (detX : P8 R) = 1 := by simp [detX,v]
  intro hz
  rw [hz,map_zero] at he
  exact zero_ne_one he

theorem typeI_map_injective [IsDomain R] (h : ℕ) :
    Function.Injective (fun p : P4 R => detY^h*pull p) := by
  intro p q hpq
  apply pull_injective
  exact mul_left_cancel₀ (pow_ne_zero h detY_ne_zero) hpq

theorem typeII_map_injective [IsDomain R] (h : ℕ) :
    Function.Injective (fun p : P4 R => detX^h*pull p) := by
  intro p q hpq
  apply pull_injective
  exact mul_left_cancel₀ (pow_ne_zero h detX_ne_zero) hpq

end AMSPhysical

#print axioms AMSPhysical.dy_power_lap_xy
#print axioms AMSPhysical.dy_power_lap_zy
#print axioms AMSPhysical.dx_power_lap_zy
#print axioms AMSPhysical.same_orientation_shift
#print axioms AMSPhysical.typeI_map_injective
#print axioms AMSPhysical.typeII_map_injective
