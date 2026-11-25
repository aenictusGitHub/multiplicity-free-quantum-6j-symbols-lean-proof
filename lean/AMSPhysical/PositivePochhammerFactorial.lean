import PochhammerQuantumFactorial

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

theorem integerQuantumProduct_positive (q : ℝ) (hq : 0<q) (hq1 : q≠1) (a k : ℕ) :
    integerQuantumProduct q ((a:ℤ)+1) k=qfactorial q (a+k)/qfactorial q a := by
  induction k with
  | zero => simp [integerQuantumProduct,qfactorial_ne_zero q hq a]
  | succ k ih =>
    rw [integerQuantumProduct_succ,ih]
    have he : (a:ℤ)+1+(k:ℤ)=((a+k+1:ℕ):ℤ) := by omega
    rw [he,← qnum_eq_qInteger q hq hq1]
    have hs : a+(k+1)=(a+k)+1 := by omega
    rw [hs,qfactorial_succ]
    ring

theorem qPochhammer_positive_factorial (q : ℝ) (hq : 0<q) (hq1 : q≠1) (a k : ℕ) :
    qPochhammer (q^2) (q^(2*((a:ℤ)+1))) k=
      (-(q-q⁻¹))^k*q^(((a:ℤ)+1)*(k:ℤ)+(k.choose 2:ℤ))*qfactorial q (a+k)/qfactorial q a := by
  rw [qPochhammer_symmetric_product q hq hq1,integerQuantumProduct_positive q hq hq1 a k]
  ring

end AMSPhysical

#print axioms AMSPhysical.qPochhammer_positive_factorial
