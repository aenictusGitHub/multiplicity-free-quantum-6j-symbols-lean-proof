import GaussianSeries
import QuantumMetric

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical

theorem qnum_add_positive (q : ℝ) (hq : 0<q) (m n : ℕ) :
    qnum q (m+n)=q^(m:ℤ)*qnum q n+q^(-(n:ℤ))*qnum q m := by
  by_cases hq1 : q=1
  · subst q
    simp only [qnum_one,one_zpow,one_mul,Nat.cast_add]
    ring
  · rw [qnum_eq_qInteger q hq hq1,qnum_eq_qInteger q hq hq1,qnum_eq_qInteger q hq hq1,
      Nat.cast_add]
    exact qInteger_add q (ne_of_gt hq) m n

theorem qnum_gaussian_step (q : ℝ) (hq : 0<q) (a r : ℕ) :
    q^((r+1:ℕ):ℤ)*qnum q (a+r+2)=
      qnum q (a+1)+q^((a+r+2:ℕ):ℤ)*qnum q (r+1) := by
  have he : a+r+2=(a+1)+(r+1) := by omega
  rw [he,qnum_add_positive q hq,mul_add,← mul_assoc,
    ← zpow_add₀ (ne_of_gt hq)]
  have hp : ((r+1:ℕ):ℤ)+((a+1:ℕ):ℤ)=(((a+1)+(r+1):ℕ):ℤ) := by omega
  rw [hp]
  have hc : q^((r+1:ℕ):ℤ)*q^(-((r+1:ℕ):ℤ))=1 := by
    rw [← zpow_add₀ (ne_of_gt hq),add_neg_cancel,zpow_zero]
  rw [← mul_assoc,hc,one_mul]
  ring

def gaussianFactorial (q : ℝ) (a r : ℕ) : ℝ :=
  q^((a*r:ℕ):ℤ)*qfactorial q (a+r)/(qfactorial q a*qfactorial q r)

theorem gaussianFactorial_zero_left (q : ℝ) (hq : 0<q) (r : ℕ) :
    gaussianFactorial q 0 r=1 := by
  simp [gaussianFactorial,qfactorial_zero,qfactorial_ne_zero q hq r]

theorem gaussianFactorial_zero_right (q : ℝ) (hq : 0<q) (a : ℕ) :
    gaussianFactorial q a 0=1 := by
  simp [gaussianFactorial,qfactorial_zero,qfactorial_ne_zero q hq a]

theorem gaussianFactorial_step (q : ℝ) (hq : 0<q) (a r : ℕ) :
    gaussianFactorial q (a+1) (r+1)=gaussianFactorial q a (r+1)+
      (q^2)^(a+1)*gaussianFactorial q (a+1) r := by
  have hpL : q^(((a+1)*(r+1):ℕ):ℤ)=
      q^((a*(r+1):ℕ):ℤ)*q^((r+1:ℕ):ℤ) := by
    rw [← zpow_add₀ (ne_of_gt hq)]
    congr 1
    push_cast
    ring
  have hpR : (q^2)^(a+1)*q^(((a+1)*r:ℕ):ℤ)=
      q^((a*(r+1):ℕ):ℤ)*q^((a+r+2:ℕ):ℤ) := by
    rw [← pow_mul,← zpow_natCast q (2*(a+1)),← zpow_add₀ (ne_of_gt hq),
      ← zpow_add₀ (ne_of_gt hq)]
    congr 1
    push_cast
    ring
  have hs1 : (a+1)+(r+1)=(a+r+1)+1 := by omega
  have hs2 : a+(r+1)=a+r+1 := by omega
  have hs3 : (a+1)+r=a+r+1 := by omega
  unfold gaussianFactorial
  rw [hs1,hs2,hs3,qfactorial_succ q (a+r+1),qfactorial_succ q a,qfactorial_succ q r,hpL]
  have hR : (q^2)^(a+1)*(q^(((a+1)*r:ℕ):ℤ)*qfactorial q (a+r+1)/
      (qfactorial q a*qnum q (a+1)*qfactorial q r))=
      (q^((a*(r+1):ℕ):ℤ)*q^((a+r+2:ℕ):ℤ))*qfactorial q (a+r+1)/
      (qfactorial q a*qnum q (a+1)*qfactorial q r) := by
    rw [← hpR]
    ring
  rw [hR]
  field_simp [qfactorial_ne_zero q hq a,qfactorial_ne_zero q hq r,
    ne_of_gt (qnum_pos q hq (a+1) (by omega)),ne_of_gt (qnum_pos q hq (r+1) (by omega))]
  linear_combination
    qfactorial q (a+r+1)*(qnum_gaussian_step q hq a r)

/-- Identification with the independently defined Gaussian generating coefficients. -/
theorem gaussianCoefficient_factorial (q : ℝ) (hq : 0<q) (a r : ℕ) :
    gaussianCoefficient (q^2) a r=gaussianFactorial q a r := by
  induction a generalizing r with
  | zero => rw [gaussianCoefficient_zero_left,gaussianFactorial_zero_left q hq]
  | succ a ih =>
    induction r with
    | zero => rw [gaussianCoefficient_zero_right,gaussianFactorial_zero_right q hq]
    | succ r ihr =>
      rw [gaussianCoefficient_step,gaussianFactorial_step q hq,ih,ihr]

end AMSPhysical

#print axioms AMSPhysical.gaussianCoefficient_factorial
