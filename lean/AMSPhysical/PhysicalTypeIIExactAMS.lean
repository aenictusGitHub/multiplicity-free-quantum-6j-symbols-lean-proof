import PhysicalTypeIICalibratedGauge

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

/-- Physical Type-II Wigner coefficient in the explicit independent shifted
channel gauge. Both vectors are actual unit vectors of the required physical
irreducible channels; no factorial formula enters their definitions. -/
def physicalTypeIICalibratedWignerSymbol (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d) (t:QuantumCupIndex a c b):ℝ:=
  (-1:ℝ)^(a+b)*physicalTypeIITripleBilin q (h+1) a b c
    (physicalTypeIICalibratedLeft q hq hq1 h a b c d hbal r).val
    (physicalTypeIICalibratedRight q hq hq1 h a b c d hbal t).val/
    Real.sqrt (twoRowIrrepQuantumDimension q hq hq1 (h+1) (by omega) ((a-r.val)+(b-r.val)) r.val*
      mixedIrrepQuantumDimension q hq hq1 (h+1) (by omega) (b-(c-t.val.val)) t.val.val)

/-- Exact literal four-triangle AMS Eq. (35) for the independently defined
physical Type-II coefficient in the specified actual channel gauge. All
ranks and admissible labels, for positive real q different from one. -/
theorem physicalTypeII_AMS_Eq35_calibrated (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d) (t:QuantumCupIndex a c b):
    physicalTypeIICalibratedWignerSymbol q hq hq1 h a b c d hbal r t=
      amsFourTrianglePrefactor q h (a:ℤ) b c d (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val)*
        AMSGeneral.kernel (quantumFactorialInt q) h true (a:ℤ) b c d
          (typeIILeftLabel a b r.val) (typeIIRightLabel b c t.val.val) := by
  rw [← typeIIShiftedReferenceWigner_AMS q hq hq1 h a b c d hbal r t]
  unfold physicalTypeIICalibratedWignerSymbol typeIIShiftedReferenceWigner
  rw [← typeIIShiftedUnitEquiv_isometry q hq hq1 h a b c d hbal,
    physicalTypeIICalibratedLeft_standard,physicalTypeIICalibratedRight_standard]
  rfl

end AMSPhysical
#print axioms AMSPhysical.physicalTypeII_AMS_Eq35_calibrated
