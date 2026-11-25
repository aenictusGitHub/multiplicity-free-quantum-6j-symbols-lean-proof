import ComplexCompatibleContinuation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open Set

def complexTypeIPhysicalMatrix (h l m c:ℕ):QuantumCupIndex l m c → QuantumCupIndex l m c → ℂ → ℂ:=
  fun s t z=>complexPhysicalTypeIWigner z h l m c s t

def complexTypeIAMSMatrix (h l m c:ℕ):QuantumCupIndex l m c → QuantumCupIndex l m c → ℂ → ℂ:=
  fun s t z=>complexAMSExpression z h false (l:ℤ) m c (l+c-m)
    (typeILeftLabel l m s.val.val) (typeIRightLabel m c t.val.val)

def complexTypeIIPhysicalMatrix (h a b c d:ℕ) (hbal:a+b=c+d):
    TypeIICommonIndex a b c d → QuantumCupIndex a c b → ℂ → ℂ:=
  fun r t z=>complexPhysicalTypeIIWigner z h a b c d hbal r t

def complexTypeIIAMSMatrix (h a b c d:ℕ):TypeIICommonIndex a b c d → QuantumCupIndex a c b → ℂ → ℂ:=
  fun r t z=>complexAMSExpression z h true (a:ℤ) b c d
    (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val)

/-- Both independently specified matrix families satisfy the exact AMS
identity throughout their constructed common connected complex branch. -/
theorem physicalTypeI_AMS_complex_matrix_branch (h l m c:ℕ) (hadm:m≤l+c):
    ∀ s t,Set.EqOn (complexTypeIPhysicalMatrix h l m c s t) (complexTypeIAMSMatrix h l m c s t)
      (complexAMSMatrixCommonBranch (complexTypeIPhysicalMatrix h l m c) (complexTypeIAMSMatrix h l m c)):=by
  apply complexAMSMatrixCommonBranch_eq
  · intro s t q hq
    exact complexPhysicalTypeIWigner_analyticAt_positive q hq h l m c s t
  · intro s t q hq
    exact complexAMSExpression_analyticAt_positive q hq _ _ _ _ _ _ _ _
  · intro s t q hq hq1
    exact (complexPhysicalTypeIWigner_ofReal_actual q hq hq1 h l m c hadm s t).trans
      ((congrArg Complex.ofReal (physicalTypeI_AMS_Eq35_four_triangles q hq hq1 h l m c hadm s t)).trans
        (complexAMSExpression_ofReal q hq _ _ _ _ _ _ _ _).symm)

theorem physicalTypeII_AMS_complex_matrix_branch (h a b c d:ℕ) (hbal:a+b=c+d):
    ∀ r t,Set.EqOn (complexTypeIIPhysicalMatrix h a b c d hbal r t) (complexTypeIIAMSMatrix h a b c d r t)
      (complexAMSMatrixCommonBranch (complexTypeIIPhysicalMatrix h a b c d hbal) (complexTypeIIAMSMatrix h a b c d)):=by
  apply complexAMSMatrixCommonBranch_eq
  · intro r t q hq
    exact complexPhysicalTypeIIWigner_analyticAt_positive q hq h a b c d hbal r t
  · intro r t q hq
    exact complexAMSExpression_analyticAt_positive q hq _ _ _ _ _ _ _ _
  · intro r t q hq hq1
    exact (complexPhysicalTypeIIWigner_ofReal_actual q hq hq1 h a b c d hbal r t).trans
      ((congrArg Complex.ofReal (physicalTypeII_AMS_Eq35_calibrated q hq hq1 h a b c d hbal r t)).trans
        (complexAMSExpression_ofReal q hq _ _ _ _ _ _ _ _).symm)

/-- Exact Type-I AMS on EVERY compatible analytic continuation of the full
matrix. Holomorphy and physical identification of the base family are proved
from independent finite CG trees and actual physical rank reduction. -/
theorem physicalTypeI_AMS_all_complex_continuations (h l m c:ℕ) (hadm:m≤l+c)
    (p:ComplexCoefficientPatch (QuantumCupIndex l m c) (QuantumCupIndex l m c))
    (hcont:ComplexCompatibleContinuation (complexTypeIPhysicalMatrix h l m c) (complexTypeIAMSMatrix h l m c)
      (complexAMSMatrixCommonBranch (complexTypeIPhysicalMatrix h l m c) (complexTypeIAMSMatrix h l m c)) p):
    ∀ s t,Set.EqOn (p.physical s t) (p.formula s t) p.domain:=
  complexCompatibleContinuation_eq _ _ _ (physicalTypeI_AMS_complex_matrix_branch h l m c hadm) p hcont

theorem physicalTypeII_AMS_all_complex_continuations (h a b c d:ℕ) (hbal:a+b=c+d)
    (p:ComplexCoefficientPatch (TypeIICommonIndex a b c d) (QuantumCupIndex a c b))
    (hcont:ComplexCompatibleContinuation (complexTypeIIPhysicalMatrix h a b c d hbal) (complexTypeIIAMSMatrix h a b c d)
      (complexAMSMatrixCommonBranch (complexTypeIIPhysicalMatrix h a b c d hbal) (complexTypeIIAMSMatrix h a b c d)) p):
    ∀ r t,Set.EqOn (p.physical r t) (p.formula r t) p.domain:=
  complexCompatibleContinuation_eq _ _ _ (physicalTypeII_AMS_complex_matrix_branch h a b c d hbal) p hcont

end AMSPhysical
#print axioms AMSPhysical.physicalTypeI_AMS_all_complex_continuations
#print axioms AMSPhysical.physicalTypeII_AMS_all_complex_continuations
