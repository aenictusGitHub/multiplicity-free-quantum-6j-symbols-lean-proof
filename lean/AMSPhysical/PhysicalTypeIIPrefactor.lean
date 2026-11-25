import PhysicalTypeIINormalization
import PositiveTwoChannelNormalization

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem typeIINormalization_prefactor (q : ℝ) (hq : 0<q) (h a b c d : ℕ)
    (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) (t : QuantumCupIndex a c b) :
    Real.sqrt (qnum q ((a-r.val)+(b-r.val)+1)*qnum q (t.val.val+(b-(c-t.val.val))+h+1))*
      Real.sqrt (typeIILeftShiftedTriangleSq q h a b c d r.val*typeIIRightShiftedTriangleSq q h a b c t.val.val)/
      Real.sqrt (typeIILeftDimension q h a b r.val*typeIIRightDimension q h b c t.val.val)=
        typeIIAMSPrefactor q h a b c d r.val t.val.val := by
  have hL : 0<typeIILeftTriangleSq q h a b c d r.val:=
    mul_pos (quantumTriangleSq_pos q hq _ _ _ _) (quantumTriangleSq_pos q hq _ _ _ _)
  have hR : 0<typeIIRightTriangleSq q h a b c t.val.val:=
    mul_pos (quantumTriangleSq_pos q hq _ _ _ _) (quantumTriangleSq_pos q hq _ _ _ _)
  have hL' : 0<typeIILeftShiftedTriangleSq q h a b c d r.val:=
    mul_pos (quantumTriangleSq_pos q hq _ _ _ _) (quantumTriangleSq_pos q hq _ _ _ _)
  have hR' : 0<typeIIRightShiftedTriangleSq q h a b c t.val.val:=
    mul_pos (quantumTriangleSq_pos q hq _ _ _ _) (quantumTriangleSq_pos q hq _ _ _ _)
  exact positiveTwoChannelNormalization
    (typeIILeftDimension q h a b r.val) (typeIIRightDimension q h b c t.val.val)
    (factorialConstant (qfactorial q) h)
    (typeIILeftTriangleSq q h a b c d r.val) (typeIIRightTriangleSq q h a b c t.val.val)
    (typeIILeftShiftedTriangleSq q h a b c d r.val) (typeIIRightShiftedTriangleSq q h a b c t.val.val)
    (qnum q ((a-r.val)+(b-r.val)+1)) (qnum q (t.val.val+(b-(c-t.val.val))+h+1))
    (sameWeyl_quantum_pos q hq h (a-r.val) (b-r.val) r.val)
    (mixedWeyl_quantum_pos q hq h t.val.val (b-(c-t.val.val)))
    (factorialConstant_quantum_pos q hq h) hL hR hL' hR'
    (qnum_pos q hq _ (by omega)) (qnum_pos q hq _ (by omega))
    ((div_eq_iff (ne_of_gt hL')).mp (typeIILeftNormalization q hq h a b c d hbal r))
    ((div_eq_iff (ne_of_gt hR')).mp (typeIIRightNormalization q hq h a b c t.val.val))

/-- Exact Type-II signed-normalization magnitude, with both higher quantum
dimensions supplied by ACTUAL restricted pivotal traces, not Weyl inputs. -/
theorem typeIIPhysicalDimensions_prefactor (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h a b c d : ℕ)
    (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) (t : QuantumCupIndex a c b) :
    Real.sqrt (qnum q ((a-r.val)+(b-r.val)+1)*qnum q (t.val.val+(b-(c-t.val.val))+h+1))*
      Real.sqrt (typeIILeftShiftedTriangleSq q h a b c d r.val*typeIIRightShiftedTriangleSq q h a b c t.val.val)/
      Real.sqrt (twoRowIrrepQuantumDimension q hq hq1 (h+1) (by omega) ((a-r.val)+(b-r.val)) r.val*
        mixedIrrepQuantumDimension q hq hq1 (h+1) (by omega) (b-(c-t.val.val)) t.val.val)=
      typeIIAMSPrefactor q h a b c d r.val t.val.val := by
  rw [← typeIILeftDimension_actual q hq hq1 h a b r.val,← typeIIRightDimension_actual q hq hq1 h b c t.val.val]
  exact typeIINormalization_prefactor q hq h a b c d hbal r t

end AMSPhysical
#print axioms AMSPhysical.typeIIPhysicalDimensions_prefactor
