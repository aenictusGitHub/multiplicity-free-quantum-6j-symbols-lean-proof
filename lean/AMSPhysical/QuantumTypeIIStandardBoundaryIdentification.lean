import TypeIIShiftedBentFamily
import TwoRowBoundaryStandardTransfer
import QuantumTypeIIHighestBoundaryInjective

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem typeIIStandardLeftHighest_eq_bent (q:ℝ) (hq:0<q) (hq1:q≠1)
    (a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d):
    typeIIStandardLeftHighest q hq hq1 a b c d hbal r=typeIIShiftedBentHighest q hq hq1 0 a b c d hbal r := by
  unfold typeIIStandardLeftHighest typeIIStandardLeftTreeMap typeIIStandardLeftPairMap
  rw [twoRowBoundaryPairMap_eq_standard]
  rfl

/-- Identification with the independently constructed standard bent vector
is an actual all-rank physical boundary theorem. -/
theorem physicalTypeIILeftHighest_boundary_standard (q:ℝ) (hq:0<q) (hq1:q≠1)
    (n:ℕ) (hn:0<n) (a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d):
    twoVertexTripleProjection n hn a b c (physicalTypeIILeftHighest q hq hq1 n hn a b c d hbal r).val=
      typeIIShiftedBentHighest q hq hq1 0 a b c d hbal r := by
  rw [physicalTypeIILeftHighest_boundary]
  exact typeIIStandardLeftHighest_eq_bent q hq hq1 a b c d hbal r

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIILeftHighest_boundary_standard
