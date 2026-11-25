import PhysicalTypeINormalization
import PositiveTwoChannelNormalization

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

theorem typeINormalization_prefactor (q : ℝ) (hq : 0<q) (h l m c s t : ℕ) :
    Real.sqrt (qnum q ((l-s)+(m-s)+h+1)*qnum q ((c-(m-t))+t+h+1))*
      Real.sqrt (typeILeftShiftedTriangleSq q h l m c s*typeIRightShiftedTriangleSq q h l m c t)/
      Real.sqrt (typeILeftDimension q h l m s*typeIRightDimension q h m c t)=
      typeIAMSPrefactor q h l m c s t := by
  exact positiveTwoChannelNormalization
    (typeILeftDimension q h l m s) (typeIRightDimension q h m c t) (factorialConstant (qfactorial q) h)
    (typeILeftTriangleSq q h l m c s) (typeIRightTriangleSq q h l m c t)
    (typeILeftShiftedTriangleSq q h l m c s) (typeIRightShiftedTriangleSq q h l m c t)
    (qnum q ((l-s)+(m-s)+h+1)) (qnum q ((c-(m-t))+t+h+1))
    (mixedWeyl_quantum_pos q hq h (l-s) (m-s)) (mixedWeyl_quantum_pos q hq h (c-(m-t)) t)
    (factorialConstant_quantum_pos q hq h) (typeILeftTriangleSq_pos q hq h l m c s)
    (typeIRightTriangleSq_pos q hq h l m c t) (typeILeftShiftedTriangleSq_pos q hq h l m c s)
    (typeIRightShiftedTriangleSq_pos q hq h l m c t)
    (qnum_pos q hq _ (by omega)) (qnum_pos q hq _ (by omega))
    ((div_eq_iff (ne_of_gt (typeILeftShiftedTriangleSq_pos q hq h l m c s))).mp (typeILeftNormalization q hq h l m c s))
    ((div_eq_iff (ne_of_gt (typeIRightShiftedTriangleSq_pos q hq h l m c t))).mp (typeIRightNormalization q hq h l m c t))

end AMSPhysical
#print axioms AMSPhysical.typeINormalization_prefactor
