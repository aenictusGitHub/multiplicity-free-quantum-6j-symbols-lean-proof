import QRacahExponentForm

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

/-- The q-Racah backward coefficient in symmetric quantum-integer notation,
including total-division boundary values. -/
theorem qRacahD_qInteger (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (a b c d r : ℤ) :
    qRacahD (q^2) (q^(2*a)) (q^(2*b)) (q^(2*c)) (q^(2*d)) (q^(2*r))=
      (q-q⁻¹)^2*q^(a+b+1)*
        (qInteger q r*qInteger q (d+r)*qInteger q (b-c-r)*qInteger q (a-c-d-r))/
          (qInteger q (c+d+2*r)*qInteger q (c+d+2*r+1)) := by
  rw [qRacahD_exponent_form q hq]
  have hnum : q^2*(1-q^(2*r))*(1-q^(2*(d+r)))*
      (q^(2*b)-q^(2*(c+r)))*(q^(2*a)-q^(2*(c+d+r)))=
      ((q-q⁻¹)^4*q^(a+b+2*c+2*d+4*r+2))*
        (qInteger q r*qInteger q (d+r)*qInteger q (b-c-r)*qInteger q (a-c-d-r)) := by
    rw [one_sub_qpow_double q hq hD,one_sub_qpow_double q hq hD,
      qpow_double_difference q hq hD,qpow_double_difference q hq hD]
    have hp : q^2*q^r*q^(d+r)*q^(b+(c+r))*q^(a+(c+d+r))=
        q^(a+b+2*c+2*d+4*r+2) := by
      rw [← zpow_natCast q 2,← zpow_add₀ hq,← zpow_add₀ hq,← zpow_add₀ hq,← zpow_add₀ hq]
      congr 1
      ring
    have h₁ : b-(c+r)=b-c-r := by ring
    have h₂ : a-(c+d+r)=a-c-d-r := by ring
    rw [h₁,h₂]
    linear_combination (q-q⁻¹)^4*
      (qInteger q r*qInteger q (d+r)*qInteger q (b-c-r)*qInteger q (a-c-d-r))*hp
  have hden : (1-q^(2*(c+d+2*r)))*(1-q^(2*(c+d+2*r+1)))=
      ((q-q⁻¹)^2*q^(2*c+2*d+4*r+1))*
        (qInteger q (c+d+2*r)*qInteger q (c+d+2*r+1)) := by
    rw [one_sub_qpow_double q hq hD,one_sub_qpow_double q hq hD]
    have hp : q^(c+d+2*r)*q^(c+d+2*r+1)=q^(2*c+2*d+4*r+1) := by
      rw [← zpow_add₀ hq]
      congr 1
      ring
    linear_combination (q-q⁻¹)^2*(qInteger q (c+d+2*r)*qInteger q (c+d+2*r+1))*hp
  have hscalar : ((q-q⁻¹)^4*q^(a+b+2*c+2*d+4*r+2))/
      ((q-q⁻¹)^2*q^(2*c+2*d+4*r+1))=(q-q⁻¹)^2*q^(a+b+1) := by
    have hp : q^(a+b+2*c+2*d+4*r+2)=q^(2*c+2*d+4*r+1)*q^(a+b+1) := by
      rw [← zpow_add₀ hq]
      congr 1
      ring
    rw [hp]
    field_simp [hD,zpow_ne_zero (2*c+2*d+4*r+1) hq]
  rw [hnum,hden,mul_div_mul_comm,hscalar]
  ring

end AMSPhysical

#print axioms AMSPhysical.qRacahD_qInteger
