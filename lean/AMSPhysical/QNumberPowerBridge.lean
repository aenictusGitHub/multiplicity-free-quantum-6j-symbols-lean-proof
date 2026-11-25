import JacobiDiagonalAlgebra
import QRacahExponentForm

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem symmetricQNumber_zpow (q : ℝ) (a : ℤ) : symmetricQNumber q (q^a)=qInteger q a := by
  unfold symmetricQNumber qInteger
  rw [zpow_neg]

theorem symmetricQNumber_mul_q (q : ℝ) (hq : q≠0) (a : ℤ) :
    symmetricQNumber q (q^a*q)=qInteger q (a+1) := by
  have hp : q^a*q=q^(a+1) := by rw [zpow_add₀ hq,zpow_one]
  rw [hp,symmetricQNumber_zpow]

theorem symmetricQNumber_div (q : ℝ) (hq : q≠0) (a b : ℤ) :
    symmetricQNumber q (q^a/q^b)=qInteger q (a-b) := by
  rw [← zpow_sub₀ hq]
  exact symmetricQNumber_zpow q (a-b)

theorem symmetricQNumber_mul_q_div (q : ℝ) (hq : q≠0) (a b : ℤ) :
    symmetricQNumber q (q^a*q/q^b)=qInteger q (a-b+1) := by
  have hp : q^a*q/q^b=q^(a-b+1) := by
    simp only [zpow_add₀ hq,zpow_sub₀ hq,zpow_one,div_eq_mul_inv]
    ring
  rw [hp,symmetricQNumber_zpow]

theorem symmetricQNumber_two_mul_q (q : ℝ) (hq : q≠0) (a b : ℤ) :
    symmetricQNumber q (q^a*q^b*q)=qInteger q (a+b+1) := by
  have hp : q^a*q^b*q=q^(a+b+1) := by rw [zpow_add₀ hq,zpow_add₀ hq,zpow_one]
  rw [hp,symmetricQNumber_zpow]

theorem symmetricQNumber_two_mul_q_div (q : ℝ) (hq : q≠0) (a b c : ℤ) :
    symmetricQNumber q (q^a*q^b*q/q^c)=qInteger q (a+b-c+1) := by
  have hp : q^a*q^b*q/q^c=q^(a+b-c+1) := by
    simp only [zpow_add₀ hq,zpow_sub₀ hq,zpow_one,div_eq_mul_inv]
    ring
  rw [hp,symmetricQNumber_zpow]

theorem symmetricQNumber_mul_q_sq (q : ℝ) (hq : q≠0) (a : ℤ) :
    symmetricQNumber q (q^a*q^2)=qInteger q (a+2) := by
  rw [← zpow_natCast q 2,← zpow_add₀ hq]
  exact symmetricQNumber_zpow q (a+2)

theorem qpow_double (q : ℝ) (hq : q≠0) (a : ℤ) : q^(2*a)=(q^a)^2 := by
  rw [zpow_squared q hq]
  congr 1
  ring

theorem qpow_div_square (q : ℝ) (hq : q≠0) (a b : ℤ) : q^a/(q^b)^2=q^(a-2*b) := by
  rw [← qpow_double q hq,← zpow_sub₀ hq]

theorem qpow_square_div (q : ℝ) (hq : q≠0) (a b : ℤ) : (q^a)^2/q^b=q^(-b+2*a) := by
  rw [← qpow_double q hq,← zpow_sub₀ hq]
  congr 1
  ring

theorem qpow_weight_pair (q : ℝ) (hq : q≠0) (m n r s : ℤ) :
    q*q^m*q^n/((q^r)^2*(q^s)^2)=q^(m+n-2*(r+s)+1) := by
  simp only [zpow_add₀ hq,zpow_sub₀ hq,zpow_one,qpow_double q hq,mul_pow,div_eq_mul_inv,mul_inv_rev]
  ring

theorem qpow_weight_pair_inv (q : ℝ) (hq : q≠0) (m n r s : ℤ) :
    (q^r)^2*(q^s)^2/(q*q^m*q^n)=q^(-(m+n-2*(r+s)+1)) := by
  have h := congrArg Inv.inv (qpow_weight_pair q hq m n r s)
  simpa only [inv_div,zpow_neg] using h

theorem qpow_scalar_casimir (q : ℝ) (hq : q≠0) (m n : ℤ) : q*q^m*q^n=q^(m+n+1) := by
  rw [zpow_add₀ hq,zpow_add₀ hq,zpow_one]
  ring

theorem qpow_square_sub_one_ne (q : ℝ) (hq : 0<q) (hq1 : q≠1) (a : ℤ) (ha : a≠0) :
    (q^a)^2-1≠0 := by
  intro hz
  have hp := sub_eq_zero.mp hz
  rw [zpow_squared q (ne_of_gt hq)] at hp
  have he : q^(a+a)=q^(0:ℤ) := by simpa only [zpow_zero] using hp
  have hi := zpow_right_injective₀ hq hq1 he
  omega

end AMSPhysical

#print axioms AMSPhysical.qpow_square_sub_one_ne
