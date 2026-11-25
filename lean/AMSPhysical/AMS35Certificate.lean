import PhysicalAMSGenericComplex
import ComplexPhysicalClassicalLimit

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

/-- Exact actual physical Type-I coefficient identity in the stated channel gauge. -/
def PhysicalTypeIAMSStatement:Prop:=
  ∀ (q:ℝ) (hq:0<q) (hq1:q≠1) (h l m c:ℕ) (hadm:m≤l+c) (s t:QuantumCupIndex l m c),
    physicalTypeIWignerSymbol q hq hq1 h l m c hadm s t=
      amsFourTrianglePrefactor q h (l:ℤ) m c (l+c-m)
        (typeILeftLabel l m s.val.val) (typeIRightLabel m c t.val.val)*
      AMSGeneral.kernel (quantumFactorialInt q) h false (l:ℤ) m c (l+c-m)
        (typeILeftLabel l m s.val.val) (typeIRightLabel m c t.val.val)

/-- Exact actual physical Type-II coefficient identity in the stated actual
unit channel gauge, with independently proved physical channel membership. -/
def PhysicalTypeIIAMSStatement:Prop:=
  ∀ (q:ℝ) (hq:0<q) (hq1:q≠1) (h a b c d:ℕ) (hbal:a+b=c+d)
    (r:TypeIICommonIndex a b c d) (t:QuantumCupIndex a c b),
    physicalTypeIICalibratedWignerSymbol q hq hq1 h a b c d hbal r t=
      amsFourTrianglePrefactor q h (a:ℤ) b c d
        (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val)*
      AMSGeneral.kernel (quantumFactorialInt q) h true (a:ℤ) b c d
        (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val)

def PhysicalTypeIClassicalAMSStatement:Prop:=
  ∀ (h l m c:ℕ) (hadm:m≤l+c) (s t:QuantumCupIndex l m c),
    physicalTypeIClassicalLimit h l m c hadm s t=
      ordinaryFourTrianglePrefactor h (l:ℤ) m c (l+c-m)
        (typeILeftLabel l m s.val.val) (typeIRightLabel m c t.val.val)*
      AMSGeneral.kernel (fun z:ℤ=>(z.toNat.factorial:ℝ)) h false (l:ℤ) m c (l+c-m)
        (typeILeftLabel l m s.val.val) (typeIRightLabel m c t.val.val)

def PhysicalTypeIIClassicalAMSStatement:Prop:=
  ∀ (h a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d) (t:QuantumCupIndex a c b),
    physicalTypeIIClassicalLimit h a b c d hbal r t=
      ordinaryFourTrianglePrefactor h (a:ℤ) b c d
        (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val)*
      AMSGeneral.kernel (fun z:ℤ=>(z.toNat.factorial:ℝ)) h true (a:ℤ) b c d
        (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val)

/-- Equality of the full maximal complex analytic coefficient continuations,
with one common whole-matrix branch and all compatible patch chains. -/
def PhysicalTypeIComplexAMSStatement:Prop:=
  ∀ (h l m c:ℕ) (hadm:m≤l+c) (q:ℂ) (v:QuantumCupIndex l m c → QuantumCupIndex l m c → ℂ),
    HasMatrixContinuationValue (complexTypeIPhysicalMatrix h l m c)
      (complexAMSMatrixCommonBranch (complexTypeIPhysicalMatrix h l m c) (complexTypeIAMSMatrix h l m c)) q v ↔
    HasMatrixContinuationValue (complexTypeIAMSMatrix h l m c)
      (complexAMSMatrixCommonBranch (complexTypeIPhysicalMatrix h l m c) (complexTypeIAMSMatrix h l m c)) q v

def PhysicalTypeIIComplexAMSStatement:Prop:=
  ∀ (h a b c d:ℕ) (hbal:a+b=c+d) (q:ℂ) (v:TypeIICommonIndex a b c d → QuantumCupIndex a c b → ℂ),
    HasMatrixContinuationValue (complexTypeIIPhysicalMatrix h a b c d hbal)
      (complexAMSMatrixCommonBranch (complexTypeIIPhysicalMatrix h a b c d hbal) (complexTypeIIAMSMatrix h a b c d)) q v ↔
    HasMatrixContinuationValue (complexTypeIIAMSMatrix h a b c d)
      (complexAMSMatrixCommonBranch (complexTypeIIPhysicalMatrix h a b c d hbal) (complexTypeIIAMSMatrix h a b c d)) q v

/-- Complete AMS Eq. (35) coefficient certificate: both physical types in all
ranks and admissible labels, their actual q=1 deformation limits, and their
full compatible complex analytic continuations. The physical base and its
CG continuation were defined independently of the AMS expression. -/
theorem AMS_Eq35_complete:PhysicalTypeIAMSStatement ∧ PhysicalTypeIIAMSStatement ∧
    PhysicalTypeIClassicalAMSStatement ∧ PhysicalTypeIIClassicalAMSStatement ∧
    PhysicalTypeIComplexAMSStatement ∧ PhysicalTypeIIComplexAMSStatement:=
  ⟨physicalTypeI_AMS_Eq35_four_triangles,physicalTypeII_AMS_Eq35_calibrated,
    physicalTypeI_classical_AMS,physicalTypeII_classical_AMS,
    physicalTypeI_AMS_Eq35_generic_complex,physicalTypeII_AMS_Eq35_generic_complex⟩

end AMSPhysical
#print axioms AMSPhysical.AMS_Eq35_complete
