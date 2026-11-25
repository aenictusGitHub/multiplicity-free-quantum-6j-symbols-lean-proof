import QRacahDeathFactor

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

def sl2RacahBirth (q : ℝ) (l m n r s : ℤ) : ℝ :=
  (q-q⁻¹)^2*qInteger q (m-r)*qInteger q s*qInteger q (l+m-2*r+n-s+1)*qInteger q (l+m-r+1)/
    (qInteger q (l+m-2*r)*qInteger q (l+m-2*r+1))

def sl2RacahDeath (q : ℝ) (l m n r s : ℤ) : ℝ :=
  (q-q⁻¹)^2*qInteger q r*qInteger q (n-s)*qInteger q (l-r+1)*qInteger q (l+m-2*r-s+1)/
    (qInteger q (l+m-2*r+1)*qInteger q (l+m-2*r+2))

/-- Exact parameter map from q-Racah forward coefficients to the physical label variables. -/
theorem qRacahB_sl2_parameters (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (l m n r s : ℤ) :
    q^(m+n+1)*qRacahB (q^2) (q^(2*(-m-1))) (q^(2*(-n-1)))
      (q^(2*(-r-s-1))) (q^(2*(r+s-l-m-1))) (q^(2*r))=sl2RacahBirth q l m n r s := by
  rw [qRacahB_qInteger q hq hD]
  have h₀ : (-m-1)+(-n-1)+1=-(m+n+1) := by ring
  have h₁ : (-m-1)+r+1=-(m-r) := by ring
  have h₂ : (-n-1)+(r+s-l-m-1)+r+1=-(l+m-2*r+n-s+1) := by ring
  have h₃ : (-r-s-1)+r+1= -s := by ring
  have h₄ : (-r-s-1)+(r+s-l-m-1)+r+1=-(l+m-r+1) := by ring
  have h₅ : (-r-s-1)+(r+s-l-m-1)+2*r+1=-(l+m-2*r+1) := by ring
  have h₆ : (-r-s-1)+(r+s-l-m-1)+2*r+2=-(l+m-2*r) := by ring
  rw [h₀,h₁,h₂,h₃,h₄,h₅,h₆]
  simp only [qInteger_neg]
  unfold sl2RacahBirth
  simp only [div_eq_mul_inv,mul_inv_rev,inv_neg]
  have hp : q^(m+n+1)*q^(-(m+n+1))=1 := by rw [← zpow_add₀ hq,add_neg_cancel,zpow_zero]
  linear_combination (q-q⁻¹)^2*qInteger q (m-r)*qInteger q s*qInteger q (l+m-2*r+n-s+1)*
    qInteger q (l+m-r+1)*(qInteger q (l+m-2*r))⁻¹*(qInteger q (l+m-2*r+1))⁻¹*hp

/-- The backward parameter map has no extra phase or dimension factor. -/
theorem qRacahD_sl2_parameters (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (l m n r s : ℤ) :
    q^(m+n+1)*qRacahD (q^2) (q^(2*(-m-1))) (q^(2*(-n-1)))
      (q^(2*(-r-s-1))) (q^(2*(r+s-l-m-1))) (q^(2*r))=sl2RacahDeath q l m n r s := by
  rw [qRacahD_qInteger q hq hD]
  have h₀ : (-m-1)+(-n-1)+1=-(m+n+1) := by ring
  have h₁ : (r+s-l-m-1)+r=-(l+m-2*r-s+1) := by ring
  have h₂ : (-n-1)-(-r-s-1)-r=-(n-s) := by ring
  have h₃ : (-m-1)-(-r-s-1)-(r+s-l-m-1)-r=l-r+1 := by ring
  have h₄ : (-r-s-1)+(r+s-l-m-1)+2*r=-(l+m-2*r+2) := by ring
  have h₅ : (-r-s-1)+(r+s-l-m-1)+2*r+1=-(l+m-2*r+1) := by ring
  rw [h₀,h₁,h₂,h₃,h₅,h₄]
  simp only [qInteger_neg]
  unfold sl2RacahDeath
  simp only [div_eq_mul_inv,mul_inv_rev,inv_neg]
  have hp : q^(m+n+1)*q^(-(m+n+1))=1 := by rw [← zpow_add₀ hq,add_neg_cancel,zpow_zero]
  linear_combination (q-q⁻¹)^2*qInteger q r*qInteger q (n-s)*qInteger q (l-r+1)*
    qInteger q (l+m-2*r-s+1)*(qInteger q (l+m-2*r+1))⁻¹*(qInteger q (l+m-2*r+2))⁻¹*hp

end AMSPhysical

#print axioms AMSPhysical.qRacahB_sl2_parameters
#print axioms AMSPhysical.qRacahD_sl2_parameters
