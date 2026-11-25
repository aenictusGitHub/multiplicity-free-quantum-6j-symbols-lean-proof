import QuantumNumbers

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical

theorem one_sub_qpow_double (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (a : ℤ) :
    1-q^(2*a)=-(q-q⁻¹)*q^a*qInteger q a := by
  have hI : (q-q⁻¹)*qInteger q a=q^a-q^(-a) := by unfold qInteger;exact mul_div_cancel₀ _ hD
  have hp : q^a*q^a=q^(2*a) := by rw [← zpow_add₀ hq];congr 1;ring
  have hi : q^a*q^(-a)=1 := by rw [← zpow_add₀ hq,add_neg_cancel,zpow_zero]
  symm
  calc
    _= -q^a*((q-q⁻¹)*qInteger q a) := by ring
    _= -q^a*(q^a-q^(-a)) := by rw [hI]
    _=_ := by linear_combination -hp+hi

theorem qpow_double_difference (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (a b : ℤ) :
    q^(2*a)-q^(2*b)=(q-q⁻¹)*q^(a+b)*qInteger q (a-b) := by
  have hI : (q-q⁻¹)*qInteger q (a-b)=q^(a-b)-q^(-(a-b)) := by unfold qInteger;exact mul_div_cancel₀ _ hD
  have hp : q^(a+b)*q^(a-b)=q^(2*a) := by rw [← zpow_add₀ hq];congr 1;ring
  have hm : q^(a+b)*q^(-(a-b))=q^(2*b) := by rw [← zpow_add₀ hq];congr 1;ring
  calc
    _=q^(a+b)*(q^(a-b)-q^(-(a-b))) := by linear_combination -hp+hm
    _=_ := by rw [← hI];ring

/-- Factorization of a four-over-two q-power quotient; no individual integer
factor is assumed nonzero, so boundary zeros retain total-division semantics. -/
theorem qInteger_four_factor_ratio (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (a b c d e f : ℤ) :
    ((1-q^(2*a))*(1-q^(2*b))*(1-q^(2*c))*(1-q^(2*d)))/
      ((1-q^(2*e))*(1-q^(2*f)))=
      (q-q⁻¹)^2*q^((a+b+c+d)-(e+f))*
        (qInteger q a*qInteger q b*qInteger q c*qInteger q d)/(qInteger q e*qInteger q f) := by
  have hp : q^a*q^b*q^c*q^d=q^(a+b+c+d) := by
    rw [← zpow_add₀ hq,← zpow_add₀ hq,← zpow_add₀ hq]
  have hn : (1-q^(2*a))*(1-q^(2*b))*(1-q^(2*c))*(1-q^(2*d))=
      ((q-q⁻¹)^4*q^(a+b+c+d))*(qInteger q a*qInteger q b*qInteger q c*qInteger q d) := by
    rw [one_sub_qpow_double q hq hD,one_sub_qpow_double q hq hD,
      one_sub_qpow_double q hq hD,one_sub_qpow_double q hq hD]
    linear_combination (q-q⁻¹)^4*(qInteger q a*qInteger q b*qInteger q c*qInteger q d)*hp
  have hden : (1-q^(2*e))*(1-q^(2*f))=
      ((q-q⁻¹)^2*q^(e+f))*(qInteger q e*qInteger q f) := by
    rw [one_sub_qpow_double q hq hD,one_sub_qpow_double q hq hD]
    have he := zpow_add₀ hq e f
    linear_combination -(q-q⁻¹)^2*(qInteger q e*qInteger q f)*he
  have hscalar : ((q-q⁻¹)^4*q^(a+b+c+d))/((q-q⁻¹)^2*q^(e+f))=
      (q-q⁻¹)^2*q^((a+b+c+d)-(e+f)) := by
    rw [zpow_sub₀ hq]
    field_simp [hD,zpow_ne_zero (e+f) hq]
  rw [hn,hden,mul_div_mul_comm,hscalar]
  ring

end AMSPhysical

#print axioms AMSPhysical.qInteger_four_factor_ratio
