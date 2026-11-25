import QuantumClebschLastFormula

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

theorem standardClebschCoefficient_first_closed (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) (a : Fin (coupledLabel l m r+1)) (z : ℕ)
    (hz : z=r.val+a.val) (hzm : z≤m) :
    standardClebschCoefficient q hq hq1 l m r a 0 z=
      (Real.sqrt (quantumHighestNorm q l m r))⁻¹*q^(-(a.val:ℤ)*(l:ℤ))*
        qfactorial q (m-r.val)*qfactorial q (coupledLabel l m r-a.val)/
          (qfactorial q (coupledLabel l m r)*qfactorial q (m-z)) := by
  have hm := channel_right_bound l m r
  have ha : a.val≤coupledLabel l m r := by have hh := a.isLt;omega
  have hma : a.val≤m-r.val := by omega
  rw [standardClebschCoefficient_first_zero q hq hq1 l m r a z,
    if_pos (by omega),← quantumHighestNorm_closed q hq hq1 l m r]
  have hmc : (m:ℤ)-(r.val:ℤ)=((m-r.val:ℕ):ℤ) := by omega
  rw [hmc,qFalling_factorial q hq hq1 (coupledLabel l m r) a.val ha,
    qFalling_factorial q hq hq1 (m-r.val) a.val hma,show m-r.val-a.val=m-z by omega]
  field_simp [qfactorial_ne_zero q hq (coupledLabel l m r),
    qfactorial_ne_zero q hq (coupledLabel l m r-a.val),qfactorial_ne_zero q hq (m-z)]

end AMSPhysical

#print axioms AMSPhysical.standardClebschCoefficient_first_closed
