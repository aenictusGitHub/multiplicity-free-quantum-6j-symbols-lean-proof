import QuantumJacobiStep
import QuantumClebschAnalytic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

def regularProjectedLeading (q : ℝ) (l m n : ℕ) (p : LeftHighestPath l m n) : ℝ :=
  (Real.sqrt (couplingNormClosed q (coupledLabel l m p.1-p.2.val) (n-p.2.val) p.2.val))⁻¹*
    (Real.sqrt (couplingNormClosed q (l-p.1.val) (m-p.1.val) p.1.val))⁻¹

theorem regularProjectedLeading_pos (q : ℝ) (hq : 0<q) (l m n : ℕ) (p : LeftHighestPath l m n) :
    0<regularProjectedLeading q l m n p :=
  mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (couplingNormClosed_pos q hq _ _ _)))
    (inv_pos.mpr (Real.sqrt_pos.mpr (couplingNormClosed_pos q hq _ _ _)))

theorem projectedLeftLeading_regular (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m n : ℕ)
    (p : LeftHighestPath l m n) : projectedLeftLeading q l m n p=regularProjectedLeading q l m n p := by
  unfold projectedLeftLeading regularProjectedLeading
  rw [quantumHighestNorm_closed q hq hq1,quantumHighestNorm_closed q hq hq1]

theorem regularProjectedLeading_sq (q : ℝ) (hq : 0<q) (l m n : ℕ) (p : LeftHighestPath l m n) :
    (regularProjectedLeading q l m n p)^2=
      (couplingNormClosed q (coupledLabel l m p.1-p.2.val) (n-p.2.val) p.2.val*
        couplingNormClosed q (l-p.1.val) (m-p.1.val) p.1.val)⁻¹ := by
  unfold regularProjectedLeading
  rw [mul_pow,inv_pow,inv_pow,Real.sq_sqrt (le_of_lt (couplingNormClosed_pos q hq _ _ _)),
    Real.sq_sqrt (le_of_lt (couplingNormClosed_pos q hq _ _ _)),mul_inv_rev]
  ring

end AMSPhysical

#print axioms AMSPhysical.projectedLeftLeading_regular
#print axioms AMSPhysical.regularProjectedLeading_sq
