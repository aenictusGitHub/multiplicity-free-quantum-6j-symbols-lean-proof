import QuantumClebschAnalytic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

def couplingDeterminantFactorialRatio (q:ℝ) (h p x r:ℕ):ℝ:=
  qfactorial q (r+h)*qfactorial q (p+x+r+h+1)*qfactorial q (p+r)*qfactorial q (x+r)/
    (qfactorial q r*qfactorial q (p+x+r+1)*qfactorial q (p+r+h)*qfactorial q (x+r+h))

/-- Exact determinant-background transformation of the proved actual
Clebsch highest norm, with its quantum-power convention retained. -/
theorem couplingNormClosed_determinant_shift (q:ℝ) (hq:0<q) (h p x r:ℕ):
    couplingNormClosed q p x (r+h)=q^(-2*(h:ℤ)*(x:ℤ))*couplingNormClosed q p x r*
      couplingDeterminantFactorialRatio q h p x r := by
  have hp:q^(-2*((r+h:ℕ):ℤ)*(x:ℤ))=q^(-2*(h:ℤ)*(x:ℤ))*q^(-2*(r:ℤ)*(x:ℤ)):=by
    rw [← zpow_add₀ (ne_of_gt hq)]
    congr 1
    push_cast
    ring
  unfold couplingNormClosed couplingDeterminantFactorialRatio
  rw [hp]
  simp only [show p+(r+h)=p+r+h from by omega,show x+(r+h)=x+r+h from by omega,
    show p+x+(r+h)+1=p+x+r+h+1 from by omega]
  have hf(k:ℕ):qfactorial q k≠0:=qfactorial_ne_zero q hq k
  field_simp [hf]

theorem couplingNormClosed_determinant_ratio (q:ℝ) (hq:0<q) (h p x r:ℕ):
    couplingNormClosed q p x (r+h)/couplingNormClosed q p x r=
      q^(-2*(h:ℤ)*(x:ℤ))*couplingDeterminantFactorialRatio q h p x r := by
  rw [couplingNormClosed_determinant_shift q hq]
  field_simp [ne_of_gt (couplingNormClosed_pos q hq p x r)]

end AMSPhysical
#print axioms AMSPhysical.couplingNormClosed_determinant_ratio
