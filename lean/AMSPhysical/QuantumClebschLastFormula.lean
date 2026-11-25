import QuantumEdgePowers
import QuantumClebschFactorial

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
open Module

/-- A closed edge coefficient obtained from the actual E-power intertwining equation. -/
theorem standardClebschCoefficient_last_cleared (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) (a : Fin (coupledLabel l m r+1)) (y : ℕ)
    (hy : a.val=(m-r.val)+y) :
    q^(-(m:ℤ)*(y:ℤ))*qfactorial q y*standardClebschCoefficient q hq hq1 l m r a y m=
      (Real.sqrt (quantumHighestNorm q l m r))⁻¹*q^(-((m-r.val:ℕ):ℤ)*(l:ℤ))*
        qfactorial q a.val*qfactorial q (l-r.val)/qfactorial q (coupledLabel l m r) := by
  have hl := channel_left_bound l m r
  have hm := channel_right_bound l m r
  have hj : m-r.val≤coupledLabel l m r := by unfold coupledLabel;omega
  let a0 : Fin (coupledLabel l m r+1) := ⟨m-r.val,by omega⟩
  have hlow : loweredWeightIndex (coupledLabel l m r) a y=a0 := by apply Fin.ext;dsimp [loweredWeightIndex,a0];omega
  have hT := unitaryQuantumClebschMap_intertwines q hq hq1 l m r ((uqGenerator q 0)^y)
    (standardWeightBasis (coupledLabel l m r) a)
  simp only [map_pow] at hT
  have hg : finiteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      (coupledLabel l m r) (uqGenerator q 0)=finiteQuantumE q (coupledLabel l m r) :=
    finiteQuantumRepresentation_generator q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      (coupledLabel l m r) 0
  rw [hg,standardWeightBasis_E_power q _ a y (by omega),hlow,map_smul] at hT
  have he := congrArg (finiteTensorCoefficient l m 0 (m:ℤ)) hT
  rw [finiteTensor_E_power_last_coefficient q hq hq1 l m y,map_smul,smul_eq_mul] at he
  change q^(-(m:ℤ)*(y:ℤ))*qfactorial q y*standardClebschCoefficient q hq hq1 l m r a y m=
    qFalling q a.val y*standardClebschCoefficient q hq hq1 l m r a0 0 m at he
  rw [standardClebschCoefficient_first_zero q hq hq1 l m r a0 m,
    if_pos (by change (m:ℤ)=(r.val:ℤ)+((m-r.val:ℕ):ℤ);omega),
    ← quantumHighestNorm_closed q hq hq1 l m r] at he
  have hmc : (m:ℤ)-(r.val:ℤ)=((m-r.val:ℕ):ℤ) := by omega
  have hay : a.val-y=m-r.val := by omega
  have hja : coupledLabel l m r-(m-r.val)=l-r.val := by unfold coupledLabel;omega
  change _=qFalling q a.val y*((Real.sqrt (quantumHighestNorm q l m r))⁻¹*
    (qFalling q (coupledLabel l m r) (m-r.val))⁻¹*q^(-((m-r.val:ℕ):ℤ)*(l:ℤ))*
      qFalling q ((m:ℤ)-(r.val:ℤ)) (m-r.val)) at he
  rw [hmc,qFalling_factorial q hq hq1 a.val y (by omega),
    qFalling_factorial q hq hq1 (coupledLabel l m r) (m-r.val) hj,
    qFalling_factorial q hq hq1 (m-r.val) (m-r.val) (le_refl _),hay,hja,Nat.sub_self,
    qfactorial_zero,div_one] at he
  calc
    _=_ := he
    _=_ := by field_simp [qfactorial_ne_zero q hq (m-r.val),qfactorial_ne_zero q hq (l-r.val),
      qfactorial_ne_zero q hq (coupledLabel l m r)]

/-- The last-weight Clebsch coefficient is a single factorial quotient, with its signed gauge fixed. -/
theorem standardClebschCoefficient_last_closed (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (r : Fin (min l m+1)) (a : Fin (coupledLabel l m r+1)) (y : ℕ)
    (hy : a.val=(m-r.val)+y) :
    standardClebschCoefficient q hq hq1 l m r a y m=
      (Real.sqrt (quantumHighestNorm q l m r))⁻¹*q^((m:ℤ)*(y:ℤ)-(l:ℤ)*((m-r.val:ℕ):ℤ))*
        qfactorial q a.val*qfactorial q (l-r.val)/(qfactorial q (coupledLabel l m r)*qfactorial q y) := by
  have he := standardClebschCoefficient_last_cleared q hq hq1 l m r a y hy
  have hphase : q^(-(m:ℤ)*(y:ℤ))*q^((m:ℤ)*(y:ℤ)-(l:ℤ)*((m-r.val:ℕ):ℤ))=
      q^(-((m-r.val:ℕ):ℤ)*(l:ℤ)) := by
    rw [← zpow_add₀ (ne_of_gt hq)]
    congr 1
    ring
  apply mul_left_cancel₀ (mul_ne_zero (zpow_ne_zero _ (ne_of_gt hq)) (qfactorial_ne_zero q hq y))
  rw [he,← hphase]
  field_simp [qfactorial_ne_zero q hq y,qfactorial_ne_zero q hq (coupledLabel l m r)]

end AMSPhysical

#print axioms AMSPhysical.standardClebschCoefficient_last_closed
