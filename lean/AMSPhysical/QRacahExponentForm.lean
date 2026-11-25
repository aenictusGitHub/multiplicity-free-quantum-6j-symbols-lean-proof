import QRacahNewtonAlgebra
import QuantumRationalFactors

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem zpow_squared (q : ℝ) (hq : q≠0) (a : ℤ) : (q^a)^2=q^(a+a) := by
  rw [sq,← zpow_add₀ hq]

theorem qRacahB_exponent_form (q : ℝ) (hq : q≠0) (a b c d r : ℤ) :
    qRacahB (q^2) (q^(2*a)) (q^(2*b)) (q^(2*c)) (q^(2*d)) (q^(2*r))=
      ((1-q^(2*(a+r+1)))*(1-q^(2*(b+d+r+1)))*(1-q^(2*(c+r+1)))*(1-q^(2*(c+d+r+1))))/
        ((1-q^(2*(c+d+2*r+1)))*(1-q^(2*(c+d+2*r+2)))) := by
  unfold qRacahB
  rw [← zpow_natCast q 2]
  simp only [zpow_squared q hq,← zpow_add₀ hq]
  congr 4 <;> ring

theorem qRacahD_exponent_form (q : ℝ) (hq : q≠0) (a b c d r : ℤ) :
    qRacahD (q^2) (q^(2*a)) (q^(2*b)) (q^(2*c)) (q^(2*d)) (q^(2*r))=
      q^2*(1-q^(2*r))*(1-q^(2*(d+r)))*
        (q^(2*b)-q^(2*(c+r)))*(q^(2*a)-q^(2*(c+d+r)))/
          ((1-q^(2*(c+d+2*r)))*(1-q^(2*(c+d+2*r+1)))) := by
  unfold qRacahD
  rw [← zpow_natCast q 2]
  simp only [zpow_squared q hq,← zpow_add₀ hq]
  congr 5 <;> ring

theorem qRacahB_qInteger (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (a b c d r : ℤ) :
    qRacahB (q^2) (q^(2*a)) (q^(2*b)) (q^(2*c)) (q^(2*d)) (q^(2*r))=
      (q-q⁻¹)^2*q^(a+b+1)*
        (qInteger q (a+r+1)*qInteger q (b+d+r+1)*qInteger q (c+r+1)*qInteger q (c+d+r+1))/
          (qInteger q (c+d+2*r+1)*qInteger q (c+d+2*r+2)) := by
  rw [qRacahB_exponent_form q hq,qInteger_four_factor_ratio q hq hD]
  have hp : ((a+r+1)+(b+d+r+1)+(c+r+1)+(c+d+r+1))-
      ((c+d+2*r+1)+(c+d+2*r+2))=a+b+1 := by ring
  rw [hp]

end AMSPhysical

#print axioms AMSPhysical.qRacahB_qInteger
