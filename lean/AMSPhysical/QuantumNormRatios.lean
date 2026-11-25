import QuantumCouplingNormFormula

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem couplingNorm_phase_step (q : ℝ) (hq : 0<q) (b r : ℕ) :
    q^(-2*((r+1:ℕ):ℤ)*(b:ℤ))=q^(2*(r:ℤ)-2*(b:ℤ))*q^(-2*(r:ℤ)*((b+1:ℕ):ℤ)) := by
  rw [← zpow_add₀ (ne_of_gt hq)]
  congr 1
  push_cast
  ring

/-- First actual coupling norm ratio, cleared so that all boundary factors are explicit. -/
theorem couplingNormClosed_outer_step (q : ℝ) (hq : 0<q) (a b r : ℕ) :
    couplingNormClosed q a b (r+1)*
      (qnum q (a+1)*qnum q (b+1)*qnum q (a+b+r+3))=
    q^(2*(r:ℤ)-2*(b:ℤ))*qnum q (r+1)*qnum q (a+b+2)*qnum q (a+b+3)*
      couplingNormClosed q (a+1) (b+1) r := by
  unfold couplingNormClosed
  have hi1 : a+b+(r+1)+1=a+b+r+2 := by omega
  have hi2 : (a+1)+(b+1)+r+1=a+b+r+3 := by omega
  have hi3 : (a+1)+(b+1)+1=a+b+3 := by omega
  have hi4 : a+(r+1)=(a+1)+r := by omega
  have hi5 : b+(r+1)=(b+1)+r := by omega
  rw [hi1,hi2,hi3,hi4,hi5,couplingNorm_phase_step q hq,
    qfactorial_succ q r,qfactorial_succ q a,qfactorial_succ q b,
    qfactorial_succ q (a+b+r+2),qfactorial_succ q (a+b+2),qfactorial_succ q (a+b+1)]
  field_simp [qfactorial_ne_zero q hq ((a+1)+r),qfactorial_ne_zero q hq ((b+1)+r),
    qfactorial_ne_zero q hq (a+b+1),ne_of_gt (qnum_pos q hq (a+b+2) (by omega)),
    ne_of_gt (qnum_pos q hq (a+b+3) (by omega))]

/-- The root coupling norm ratio used when the inner channel decreases by one. -/
theorem couplingNormClosed_root_step (q : ℝ) (hq : 0<q) (a b s : ℕ) :
    couplingNormClosed q (a+1) b (s+1)*
      (qnum q (b+1)*qnum q (a+s+1)*qnum q (a+s+2))=
    q^(2*(s:ℤ)-2*(b:ℤ))*qnum q (s+1)*qnum q (a+1)*qnum q (a+b+s+3)*
      couplingNormClosed q a (b+1) s := by
  unfold couplingNormClosed
  have hi1 : (a+1)+b+(s+1)+1=a+b+s+3 := by omega
  have hi2 : a+(b+1)+s+1=a+b+s+2 := by omega
  have hi3 : (a+1)+b+1=a+(b+1)+1 := by omega
  have hi4 : (a+1)+(s+1)=a+s+2 := by omega
  have hi5 : b+(s+1)=(b+1)+s := by omega
  rw [hi1,hi2,hi3,hi4,hi5,couplingNorm_phase_step q hq,
    qfactorial_succ q s,qfactorial_succ q a,qfactorial_succ q b,
    qfactorial_succ q (a+b+s+2),qfactorial_succ q (a+s+1),qfactorial_succ q (a+s)]
  field_simp [qfactorial_ne_zero q hq (a+s),qfactorial_ne_zero q hq ((b+1)+s),
    qfactorial_ne_zero q hq (a+(b+1)+1),ne_of_gt (qnum_pos q hq (a+s+1) (by omega)),
    ne_of_gt (qnum_pos q hq (a+s+2) (by omega))]

end AMSPhysical

#print axioms AMSPhysical.couplingNormClosed_outer_step
#print axioms AMSPhysical.couplingNormClosed_root_step
