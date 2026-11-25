import QuantumCouplingDeterminantNorm
import QuantumTwoRowDimensionClosed
import QuantumMixedIrrepDimension

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical

/-- Common physical metric factor for the determinant-background transport.
It is independent of the intermediate channel. -/
def typeIIDeterminantMetricScale (q:ℝ) (h a b d:ℕ):ℝ:=
  q^(-2*(h:ℤ)*(b:ℤ))*qfactorial q h*qfactorial q a*qfactorial q b*qfactorial q (d+h+1)/
    (qfactorial q (a+h)*qfactorial q (b+h)*qfactorial q (d+1))

theorem typeIIDeterminantMetricScale_pos (q:ℝ) (hq:0<q) (h a b d:ℕ):
    0<typeIIDeterminantMetricScale q h a b d :=
  div_pos (mul_pos (mul_pos (mul_pos (mul_pos (zpow_pos hq _) (qfactorial_pos q hq _))
    (qfactorial_pos q hq _)) (qfactorial_pos q hq _)) (qfactorial_pos q hq _))
    (mul_pos (mul_pos (qfactorial_pos q hq _) (qfactorial_pos q hq _)) (qfactorial_pos q hq _))

/-- Channel-independent determinant metric normalization derived from the
actual Clebsch norm and the actual higher-rank two-row pivotal dimension.
This is a scalar identity; vector-space metric transport is separate. -/
theorem typeIIDeterminantMetricScale_channel (q:ℝ) (hq:0<q) (hq1:q≠1) (h p x r d:ℕ):
    (q^(-(h:ℤ)*(r:ℤ)))^2*
      (couplingNormClosed q p x (r+h)/couplingNormClosed q p x r)*
      (qnum q (p+x+1)/qnum q (d+1))=
    typeIIDeterminantMetricScale q h (p+r) (x+r) d*
      (twoRowIrrepQuantumDimension q hq hq1 (h+1) (by omega) (p+x) r/symmetricQuantumDimension q (h+1) d) := by
  rw [couplingNormClosed_determinant_ratio q hq]
  have hp:(q^(-(h:ℤ)*(r:ℤ)))^2*q^(-2*(h:ℤ)*(x:ℤ))=q^(-2*(h:ℤ)*((x+r:ℕ):ℤ)):=by
    rw [sq,← zpow_add₀ (ne_of_gt hq),← zpow_add₀ (ne_of_gt hq)]
    congr 1
    push_cast
    ring
  calc
    _=q^(-2*(h:ℤ)*((x+r:ℕ):ℤ))*couplingDeterminantFactorialRatio q h p x r*
        (qnum q (p+x+1)/qnum q (d+1)):=by rw [← hp];ring
    _=_:=by
      rw [twoRowIrrepQuantumDimension_closed q hq hq1]
      unfold typeIIDeterminantMetricScale couplingDeterminantFactorialRatio symmetricQuantumDimension
      rw [show r+(h+1)-1=r+h from by omega,show h+1-1=h from by omega,
        show p+x+r+(h+1)=p+x+r+h+1 from by omega,
        show h+1+d=d+h+1 from by omega,qfactorial_succ q d]
      have hf(k:ℕ):qfactorial q k≠0:=qfactorial_ne_zero q hq k
      have hd:qnum q (d+1)≠0:=ne_of_gt (qnum_pos q hq (d+1) (by omega))
      field_simp [hf,hd]
    
end AMSPhysical
#print axioms AMSPhysical.typeIIDeterminantMetricScale_channel
