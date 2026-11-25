import GaussianFactorial

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 700000
noncomputable section
namespace AMSPhysical

theorem qFactorial_eq_qfactorial (q : ℝ) (hq : 0<q) (hq1 : q≠1) (k : ℕ) :
    qFactorial q k=qfactorial q k := by
  induction k with
  | zero => exact (qfactorial_zero q).symm
  | succ k ih => rw [qFactorial,ih,← qnum_eq_qInteger q hq hq1,qfactorial_succ]

theorem qFalling_mul_factorial (q : ℝ) (hq : 0<q) (hq1 : q≠1) (r k : ℕ) (hk : k≤r) :
    qFalling q (r:ℤ) k*qfactorial q (r-k)=qfactorial q r := by
  induction k with
  | zero => simp only [qFalling,Nat.sub_zero,one_mul]
  | succ k ih =>
    have hs : r-k=(r-(k+1))+1 := by omega
    have hc : (r:ℤ)-(k:ℤ)=((r-k:ℕ):ℤ) := by omega
    rw [qFalling,hc,← qnum_eq_qInteger q hq hq1,mul_assoc]
    have hfac : qnum q (r-k)*qfactorial q (r-(k+1))=qfactorial q (r-k) := by
      conv_rhs => rw [hs,qfactorial_succ]
      rw [← hs]
      ring
    rw [hfac]
    exact ih (by omega)

theorem qFalling_factorial (q : ℝ) (hq : 0<q) (hq1 : q≠1) (r k : ℕ) (hk : k≤r) :
    qFalling q (r:ℤ) k=qfactorial q r/qfactorial q (r-k) :=
  (eq_div_iff (qfactorial_ne_zero q hq (r-k))).mpr (qFalling_mul_factorial q hq hq1 r k hk)

theorem couplingCoefficient_factorial (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (m : ℤ) (r k : ℕ) (hk : k≤r) :
    couplingCoefficient q m r k=(-1:ℝ)^k*q^(couplingExponent m r k)*qfactorial q r/
      (qfactorial q k*qfactorial q (r-k)) := by
  rw [couplingCoefficient_closed q (ne_of_gt hq),qFalling_factorial q hq hq1 r k hk,
    qFactorial_eq_qfactorial q hq hq1]
  ring

theorem gaussianFactorial_vandermonde (q : ℝ) (hq : 0<q) (a b r : ℕ) :
    gaussianFactorial q (a+b+1) r=
      ∑ ij∈Finset.antidiagonal r,
        gaussianFactorial q b ij.1*((q^2)^(b+1))^ij.2*gaussianFactorial q a ij.2 := by
  rw [← gaussianCoefficient_factorial q hq (a+b+1) r,gaussian_vandermonde]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [gaussianCoefficient_factorial q hq b ij.1,gaussianCoefficient_factorial q hq a ij.2]

end AMSPhysical

#print axioms AMSPhysical.couplingCoefficient_factorial
#print axioms AMSPhysical.gaussianFactorial_vandermonde
