import PhysicalAMSComplexContinuation
import ComplexMatrixContinuationSpace

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

/-- AMS Eq. (35) as equality of the FULL analytic-continuation families.
For every complex parameter and every whole-matrix value, the independent
physical CG continuation has that value iff the literal AMS expression has
that value on the same analytic continuation. The physical base family was
constructed without the AMS candidate and identified with actual all-rank
physical couplings. -/
theorem physicalTypeI_AMS_Eq35_generic_complex (h l m c:ℕ) (hadm:m≤l+c)
    (q:ℂ) (v:QuantumCupIndex l m c → QuantumCupIndex l m c → ℂ):
    HasMatrixContinuationValue (complexTypeIPhysicalMatrix h l m c)
      (complexAMSMatrixCommonBranch (complexTypeIPhysicalMatrix h l m c) (complexTypeIAMSMatrix h l m c)) q v ↔
    HasMatrixContinuationValue (complexTypeIAMSMatrix h l m c)
      (complexAMSMatrixCommonBranch (complexTypeIPhysicalMatrix h l m c) (complexTypeIAMSMatrix h l m c)) q v:=
  matrixContinuationValues_same_germ _ _ _ (physicalTypeI_AMS_complex_matrix_branch h l m c hadm) q v

theorem physicalTypeII_AMS_Eq35_generic_complex (h a b c d:ℕ) (hbal:a+b=c+d)
    (q:ℂ) (v:TypeIICommonIndex a b c d → QuantumCupIndex a c b → ℂ):
    HasMatrixContinuationValue (complexTypeIIPhysicalMatrix h a b c d hbal)
      (complexAMSMatrixCommonBranch (complexTypeIIPhysicalMatrix h a b c d hbal) (complexTypeIIAMSMatrix h a b c d)) q v ↔
    HasMatrixContinuationValue (complexTypeIIAMSMatrix h a b c d)
      (complexAMSMatrixCommonBranch (complexTypeIIPhysicalMatrix h a b c d hbal) (complexTypeIIAMSMatrix h a b c d)) q v:=
  matrixContinuationValues_same_germ _ _ _ (physicalTypeII_AMS_complex_matrix_branch h a b c d hbal) q v

/-- Stronger branch statement: the very same complete continuation patch,
not just the set of point values, is a physical continuation iff it is an
AMS continuation. -/
theorem physicalTypeII_AMS_same_complex_branches (h a b c d:ℕ) (hbal:a+b=c+d)
    (p:HolomorphicMatrixPatch (TypeIICommonIndex a b c d) (QuantumCupIndex a c b)):
    IsMatrixContinuation (complexTypeIIPhysicalMatrix h a b c d hbal)
      (complexAMSMatrixCommonBranch (complexTypeIIPhysicalMatrix h a b c d hbal) (complexTypeIIAMSMatrix h a b c d)) p ↔
    IsMatrixContinuation (complexTypeIIAMSMatrix h a b c d)
      (complexAMSMatrixCommonBranch (complexTypeIIPhysicalMatrix h a b c d hbal) (complexTypeIIAMSMatrix h a b c d)) p:=
  matrixContinuation_same_germ _ _ _ (physicalTypeII_AMS_complex_matrix_branch h a b c d hbal) p

end AMSPhysical
#print axioms AMSPhysical.physicalTypeI_AMS_Eq35_generic_complex
#print axioms AMSPhysical.physicalTypeII_AMS_Eq35_generic_complex
