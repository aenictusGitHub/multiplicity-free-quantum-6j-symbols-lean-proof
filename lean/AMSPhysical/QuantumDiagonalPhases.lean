import QuantumJacobiDiagonal

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

def sl2DiagonalWeight (q : ℝ) (m n r s : ℤ) : ℝ :=
  (q-q⁻¹)^2*(qInteger q (m-r+1)*qInteger q r*q^(n-2*s)+
    q^(-m+2*r)*qInteger q (n-s+1)*qInteger q s)+
      q^(m+n-2*(r+s)+1)+q^(-(m+n-2*(r+s)+1))

def sl2ProjectedDiagonal (q : ℝ) (i m n r s : ℤ) : ℝ :=
  sl2DiagonalWeight q m n r s-
    (q-q⁻¹)^2*q^(-i)*qInteger q (n-s+1)*qInteger q (r+1)*qInteger q s*qInteger q (m-r)/qInteger q i+
    (q-q⁻¹)^2*q^(-i-2)*qInteger q r*qInteger q (n-s)*qInteger q (s+1)*qInteger q (m-r+1)/qInteger q (i+2)

theorem casimirDiagonalWeight_integer (q : ℝ) (hq : q≠0) (m n r s : ℕ) :
    casimirDiagonalWeight q m n r s=sl2DiagonalWeight q m n r s := by
  unfold casimirDiagonalWeight sl2DiagonalWeight
  have hp : q*q^((m:ℤ)+(n:ℤ)-2*((r:ℤ)+(s:ℤ)))=
      q^((m:ℤ)+(n:ℤ)-2*((r:ℤ)+(s:ℤ))+1) := by
    rw [zpow_add₀ hq,zpow_one]
    ring
  have hm : q⁻¹*q^(-((m:ℤ)+(n:ℤ)-2*((r:ℤ)+(s:ℤ))))=
      q^(-((m:ℤ)+(n:ℤ)-2*((r:ℤ)+(s:ℤ))+1)) := by
    rw [← zpow_neg_one,← zpow_add₀ hq]
    congr 1
    ring
  rw [hp,hm]

theorem casimirUpperInputStep_nextRatio (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (p : LeftHighestPath l m n) :
    casimirUpperInputStep q m n p.1.val p.2.val*projectedLeftNextRatio q l m n p=
      -(q-q⁻¹)^2*q^(-(coupledLabel l m p.1:ℤ))*qInteger q ((n:ℤ)-(p.2.val:ℤ)+1)*
        qInteger q ((p.1.val:ℤ)+1)*qInteger q (p.2.val:ℤ)*qInteger q ((m:ℤ)-(p.1.val:ℤ))/
          qInteger q (coupledLabel l m p.1:ℤ) := by
  rw [projectedLeftNextRatio_closed q hq hq1]
  unfold casimirUpperInputStep
  simp only [div_eq_mul_inv]
  have hp : q^(-(m:ℤ)+2*(p.1.val:ℤ))*q^((n:ℤ)-2*((p.2.val:ℤ)-1))*
      q^(-(l:ℤ)-(n:ℤ)+2*(p.2.val:ℤ)-2)=q^(-(coupledLabel l m p.1:ℤ)) := by
    rw [← zpow_add₀ (ne_of_gt hq),← zpow_add₀ (ne_of_gt hq)]
    congr 1
    rw [coupledLabel_cast l m p.1.val (channel_left_bound l m p.1) (channel_right_bound l m p.1)]
    ring
  linear_combination -(q-q⁻¹)^2*qInteger q ((n:ℤ)-(p.2.val:ℤ)+1)*qInteger q ((p.1.val:ℤ)+1)*
    qInteger q (p.2.val:ℤ)*qInteger q ((m:ℤ)-(p.1.val:ℤ))*(qInteger q (coupledLabel l m p.1:ℤ))⁻¹*hp

theorem casimirLowerStep_previousRatio (q : ℝ) (hq : 0<q) (l m n : ℕ)
    (p : LeftHighestPath l m n) :
    casimirLowerStep q m n p.1.val p.2.val*previousProjectedNextRatio q l m n p=
      -(q-q⁻¹)^2*q^(-(coupledLabel l m p.1:ℤ)-2)*qInteger q (p.1.val:ℤ)*
        qInteger q ((n:ℤ)-(p.2.val:ℤ))*qInteger q ((p.2.val:ℤ)+1)*qInteger q ((m:ℤ)-(p.1.val:ℤ)+1)/
          qInteger q ((coupledLabel l m p.1:ℤ)+2) := by
  unfold casimirLowerStep previousProjectedNextRatio
  simp only [div_eq_mul_inv]
  have hp : q^(-(m:ℤ)+2*((p.1.val:ℤ)-1))*q^((n:ℤ)-2*(p.2.val:ℤ))*
      q^(-(l:ℤ)-(n:ℤ)+2*(p.2.val:ℤ))=q^(-(coupledLabel l m p.1:ℤ)-2) := by
    rw [← zpow_add₀ (ne_of_gt hq),← zpow_add₀ (ne_of_gt hq)]
    congr 1
    rw [coupledLabel_cast l m p.1.val (channel_left_bound l m p.1) (channel_right_bound l m p.1)]
    ring
  linear_combination -(q-q⁻¹)^2*qInteger q (p.1.val:ℤ)*qInteger q ((n:ℤ)-(p.2.val:ℤ))*
    qInteger q ((p.2.val:ℤ)+1)*qInteger q ((m:ℤ)-(p.1.val:ℤ)+1)*
      (qInteger q ((coupledLabel l m p.1:ℤ)+2))⁻¹*hp

theorem casimirJacobiDiagonalClosed_integer (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (p : LeftHighestPath l m n) :
    casimirJacobiDiagonalClosed q l m n p=sl2ProjectedDiagonal q (coupledLabel l m p.1) m n p.1.val p.2.val := by
  unfold casimirJacobiDiagonalClosed
  rw [casimirDiagonalWeight_integer q (ne_of_gt hq),casimirUpperInputStep_nextRatio q hq hq1,
    casimirLowerStep_previousRatio q hq]
  unfold sl2ProjectedDiagonal
  ring

end AMSPhysical

#print axioms AMSPhysical.casimirJacobiDiagonalClosed_integer
