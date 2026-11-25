import QuantumClebsch

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
noncomputable section
namespace AMSPhysical

variable {K : Type*} [Field K]

def qFactorial (q : K) : ℕ → K
  | 0 => 1
  | k+1 => qFactorial q k*qInteger q (k+1:ℕ)

def couplingExponent (m : ℤ) (r k : ℕ) : ℤ := (k:ℤ)*(-m+2*r-k-1)

theorem couplingExponent_step (m : ℤ) (r k : ℕ) :
    couplingExponent m r (k+1)=couplingExponent m r k+(-(m-2*((r:ℤ)-k-1))) := by
  simp only [couplingExponent,Nat.cast_add,Nat.cast_one]
  ring

/-- Closed quantum-factorial expression for the actual highest-weight recurrence. -/
theorem couplingCoefficient_closed (q : K) (hq : q≠0) (m : ℤ) (r k : ℕ) :
    couplingCoefficient q m r k=
      (-1)^k*q^(couplingExponent m r k)*qFalling q r k/qFactorial q k := by
  induction k with
  | zero => simp only [couplingCoefficient,pow_zero,couplingExponent,Nat.cast_zero,
      zero_mul,zpow_zero,one_mul,qFalling,qFactorial,div_one]
  | succ k ih =>
    rw [couplingCoefficient,ih,pow_succ,couplingExponent_step,zpow_add₀ hq,qFalling,qFactorial]
    simp only [div_eq_mul_inv,mul_inv_rev,zpow_neg]
    ring

theorem qFactorial_ne_zero (q : K) (k : ℕ)
    (hq : ∀ j : ℕ,0<j → j≤k → qInteger q j≠0) : qFactorial q k≠0 := by
  induction k with
  | zero => exact one_ne_zero
  | succ k ih =>
    rw [qFactorial]
    exact mul_ne_zero (ih (fun j hj hjk => hq j hj (by omega))) (hq (k+1) (by omega) le_rfl)

end AMSPhysical

#print axioms AMSPhysical.couplingCoefficient_closed
