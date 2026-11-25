import TypeIIShiftedUnitEquivalence
import QuantumTypeIIRightBasis

set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
namespace AMSPhysical

theorem typeIIShiftedUnitEquiv_right_unit (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (t:QuantumCupIndex a c b):
    quantumTripleBilin q (a+h) (b+h) c
      (typeIIShiftedUnitEquiv q hq hq1 h a b c d hbal
        (physicalTypeIIRightCoupling q hq hq1 (h+1) (by omega) a b c d hbal t)).val
      (typeIIShiftedUnitEquiv q hq hq1 h a b c d hbal
        (physicalTypeIIRightCoupling q hq hq1 (h+1) (by omega) a b c d hbal t)).val=1 := by
  rw [typeIIShiftedUnitEquiv_isometry,physicalTypeIIRightCoupling_pair,if_pos rfl]

end AMSPhysical
#print axioms AMSPhysical.typeIIShiftedUnitEquiv_right_unit
