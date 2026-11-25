import TypeIIShiftedPhysicalKernel
import AMSTypeIITriangleCoordinates
import QuantumTypeIIRecoupling

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

/-- Actual higher-rank physical Type-II Wigner coefficient, defined ONLY
from independent physical channel overlaps and actual pivotal dimensions. -/
def physicalTypeIIWignerSymbol (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h a b c d : ℕ)
    (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) (t : QuantumCupIndex a c b) : ℝ :=
  (-1:ℝ)^(a+b)*physicalTypeIIRecouplingMatrix q hq hq1 (h+1) (by omega) a b c d hbal r t /
    Real.sqrt (twoRowIrrepQuantumDimension q hq hq1 (h+1) (by omega) ((a-r.val)+(b-r.val)) r.val*
      mixedIrrepQuantumDimension q hq hq1 (h+1) (by omega) (b-(c-t.val.val)) t.val.val)

/-- The independently constructed shifted STANDARD sl2 overlap, normalized
by the actual higher physical dimensions. It is a reference quantity, not
a definition of the higher-rank physical Type-II Wigner coefficient. -/
def typeIIShiftedReferenceWigner (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h a b c d : ℕ)
    (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) (t : QuantumCupIndex a c b) : ℝ :=
  (-1:ℝ)^(a+b)*quantumRacahMatrix q hq hq1 (a+h) (b+h) c
    (typeIIShiftedLeftPath h a b c d hbal r) (typeIIShiftedRightPath h a b c t) /
    Real.sqrt (twoRowIrrepQuantumDimension q hq hq1 (h+1) (by omega) ((a-r.val)+(b-r.val)) r.val*
      mixedIrrepQuantumDimension q hq hq1 (h+1) (by omega) (b-(c-t.val.val)) t.val.val)

/-- All Type-II scalar and physical-dimension normalization obligations are
closed: the shifted actual sl2 reference is exactly the literal source AMS
four-triangle factorial expression. The separate higher overlap equality
is NOT asserted here. -/
theorem typeIIShiftedReferenceWigner_AMS (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h a b c d : ℕ)
    (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) (t : QuantumCupIndex a c b) :
    typeIIShiftedReferenceWigner q hq hq1 h a b c d hbal r t=
      amsFourTrianglePrefactor q h (a:ℤ) b c d (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val)*
        AMSGeneral.kernel (quantumFactorialInt q) h true (a:ℤ) b c d
          (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val) := by
  unfold typeIIShiftedReferenceWigner
  rw [typeIIShifted_physicalRacah_kernel q hq hq1 h a b c d hbal r t]
  have hNorm:=typeIIPhysicalDimensions_prefactor q hq hq1 h a b c d hbal r t
  rw [show t.val.val+(b-(c-t.val.val))=(b-(c-t.val.val))+t.val.val from by omega] at hNorm
  change Real.sqrt (qnum q (typeIILeftLabel a b r.val+1)*qnum q (typeIIRightLabel b c t.val.val+h+1))*
    Real.sqrt (typeIILeftShiftedTriangleSq q h a b c d r.val*typeIIRightShiftedTriangleSq q h a b c t.val.val)/
    Real.sqrt (twoRowIrrepQuantumDimension q hq hq1 (h+1) (by omega) ((a-r.val)+(b-r.val)) r.val*
      mixedIrrepQuantumDimension q hq hq1 (h+1) (by omega) (b-(c-t.val.val)) t.val.val)=_ at hNorm
  rw [typeIIAMSPrefactor_four_triangles q h a b c d hbal] at hNorm
  calc
    _ = ((-1:ℝ)^(a+b)*(-1:ℝ)^(a+b))*
      (Real.sqrt (qnum q (typeIILeftLabel a b r.val+1)*qnum q (typeIIRightLabel b c t.val.val+h+1))*
        Real.sqrt (typeIILeftShiftedTriangleSq q h a b c d r.val*typeIIRightShiftedTriangleSq q h a b c t.val.val)/
        Real.sqrt (twoRowIrrepQuantumDimension q hq hq1 (h+1) (by omega) ((a-r.val)+(b-r.val)) r.val*
          mixedIrrepQuantumDimension q hq hq1 (h+1) (by omega) (b-(c-t.val.val)) t.val.val))*
      AMSGeneral.kernel (quantumFactorialInt q) h true (a:ℤ) b c d
        (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val) := by ring
    _ = _ := by rw [AMSGeneral.sign_square,one_mul,hNorm]

end AMSPhysical
#print axioms AMSPhysical.typeIIShiftedReferenceWigner_AMS
