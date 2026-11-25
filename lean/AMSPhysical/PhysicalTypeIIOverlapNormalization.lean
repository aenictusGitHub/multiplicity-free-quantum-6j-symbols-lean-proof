import PhysicalTypeIICalibratedGauge

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

/-- Actual overlap and pivotal-dimension normalization, used to construct
complex continuation before comparing it with any AMS expression. -/
theorem physicalTypeIICalibrated_overlap_normalization (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d) (t:QuantumCupIndex a c b):
    (-1:ℝ)^(a+b)*physicalTypeIITripleBilin q (h+1) a b c
      (physicalTypeIICalibratedLeft q hq hq1 h a b c d hbal r).val
      (physicalTypeIICalibratedRight q hq hq1 h a b c d hbal t).val/
      Real.sqrt (sameWeyl (qfactorial q) (qnum q) h (a-r.val) (b-r.val) r.val*
        mixedWeyl (qfactorial q) (qnum q) h (b-(c-t.val.val)) t.val.val)=
      (-1:ℝ)^(a+b)*quantumRacahMatrix q hq hq1 (a+h) (b+h) c
        (typeIIShiftedLeftPath h a b c d hbal r) (typeIIShiftedRightPath h a b c t)/
      Real.sqrt (sameWeyl (qfactorial q) (qnum q) h (a-r.val) (b-r.val) r.val*
        mixedWeyl (qfactorial q) (qnum q) h (b-(c-t.val.val)) t.val.val) := by
  rw [← typeIIShiftedUnitEquiv_isometry q hq hq1 h a b c d hbal,
    physicalTypeIICalibratedLeft_standard,physicalTypeIICalibratedRight_standard]
  rfl

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIICalibrated_overlap_normalization
