import ActualAMSRecoupling
import SharedActualAMSUnitary
import AMSTriangleCoordinates
import PhysicalTypeIIExactAMS

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

/-- Wigner coefficient of the single actual trivalent table. The only
normalization is the prescribed exterior sign and actual pivotal dimensions;
no AMS factorial expression or independently chosen channel phase occurs. -/
def actualTypeIWignerSymbol (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h : ℕ) (hh : 1≤h)
    (l m c : ℕ) (s t : QuantumCupIndex l m c) : ℝ :=
  (-1:ℝ)^(l+c)*actualTypeIRecouplingMatrix q hq hq1 h hh l m c s t /
    Real.sqrt (mixedIrrepQuantumDimension q hq hq1 (h+1) (by omega) (l-s.val.val) (m-s.val.val)*
      mixedIrrepQuantumDimension q hq hq1 (h+1) (by omega) (c-(m-t.val.val)) t.val.val)

def actualTypeIIWignerSymbol (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h : ℕ) (hh : 1≤h)
    (a b c d : ℕ) (r : TypeIICommonIndex a b c d) (t : QuantumCupIndex a c b) : ℝ :=
  (-1:ℝ)^(a+b)*actualTypeIIRecouplingMatrix q hq hq1 h hh a b c d r t /
    Real.sqrt (twoRowIrrepQuantumDimension q hq hq1 (h+1) (by omega) ((a-r.val)+(b-r.val)) r.val*
      mixedIrrepQuantumDimension q hq hq1 (h+1) (by omega) (b-(c-t.val.val)) t.val.val)

theorem actualTypeIWignerSymbol_eq_calibrated (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h : ℕ) (hh : 1≤h) (l m c : ℕ) (hadm : m≤l+c) (s t : QuantumCupIndex l m c) :
    actualTypeIWignerSymbol q hq hq1 h hh l m c s t=physicalTypeIWignerSymbol q hq hq1 h l m c hadm s t := by
  unfold actualTypeIWignerSymbol physicalTypeIWignerSymbol
  rw [actualTypeIRecouplingMatrix_calibrated q hq hq1 h hh l m c hadm]

theorem actualTypeIIWignerSymbol_eq_calibrated (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h : ℕ) (hh : 1≤h) (a b c d : ℕ) (hbal : a+b=c+d)
    (r : TypeIICommonIndex a b c d) (t : QuantumCupIndex a c b) :
    actualTypeIIWignerSymbol q hq hq1 h hh a b c d r t=
      physicalTypeIICalibratedWignerSymbol q hq hq1 h a b c d hbal r t := by
  unfold actualTypeIIWignerSymbol physicalTypeIICalibratedWignerSymbol
  rw [actualTypeIIRecouplingMatrix_calibrated q hq hq1 h hh a b c d hbal]

/-- Both families use amsActualVertexTable on actual Dynkin triples, with
all six full intertwiner roles and their isometry certified separately. -/
theorem actualTypeI_AMS_Eq35_shared_vertices (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h : ℕ) (hh : 1≤h) (l m c : ℕ) (hadm : m≤l+c) (s t : QuantumCupIndex l m c) :
    actualTypeIWignerSymbol q hq hq1 h hh l m c s t=
      amsFourTrianglePrefactor q h (l:ℤ) m c (l+c-m)
        (typeILeftLabel l m s.val.val) (typeIRightLabel m c t.val.val)*
      AMSGeneral.kernel (quantumFactorialInt q) h false (l:ℤ) m c (l+c-m)
        (typeILeftLabel l m s.val.val) (typeIRightLabel m c t.val.val) := by
  rw [actualTypeIWignerSymbol_eq_calibrated q hq hq1 h hh l m c hadm]
  exact physicalTypeI_AMS_Eq35_four_triangles q hq hq1 h l m c hadm s t

theorem actualTypeII_AMS_Eq35_shared_vertices (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (h : ℕ) (hh : 1≤h) (a b c d : ℕ) (hbal : a+b=c+d)
    (r : TypeIICommonIndex a b c d) (t : QuantumCupIndex a c b) :
    actualTypeIIWignerSymbol q hq hq1 h hh a b c d r t=
      amsFourTrianglePrefactor q h (a:ℤ) b c d (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val)*
        AMSGeneral.kernel (quantumFactorialInt q) h true (a:ℤ) b c d
          (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val) := by
  rw [actualTypeIIWignerSymbol_eq_calibrated q hq hq1 h hh a b c d hbal]
  exact physicalTypeII_AMS_Eq35_calibrated q hq hq1 h a b c d hbal r t

end AMSPhysical
#print axioms AMSPhysical.actualTypeI_AMS_Eq35_shared_vertices
#print axioms AMSPhysical.actualTypeII_AMS_Eq35_shared_vertices
