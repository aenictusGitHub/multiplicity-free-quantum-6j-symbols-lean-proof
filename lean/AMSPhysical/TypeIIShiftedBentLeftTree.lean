import StandardBentLeftTree
import StandardBentPairLabel
import TypeIIShiftedBentFamily
import TypeIIShiftedPaths

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

/-- Exact whole-vector identification at the AMS shifted labels. -/
theorem typeIIShiftedBentHighest_eq_leftTree (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d):
    typeIIShiftedBentHighest q hq hq1 h a b c d hbal r=
      (((-1:ℝ)^(r.val:ℤ))*Real.sqrt (quantumHighestNorm q
        (coupledLabel (a+h) (b+h) (typeIIShiftedLeftPath h a b c d hbal r).1) c
        (typeIIShiftedLeftPath h a b c d hbal r).2)/
        Real.sqrt (quantumHighestNorm q d c (typeIIBentSourceIndex a b c d r))) •
      standardTypeIIBoundaryEquiv (a+h) (b+h) c
        (quantumLeftTreeHighest q hq hq1 (a+h) (b+h) c
          (typeIIShiftedLeftPath h a b c d hbal r).1
          (typeIIShiftedLeftPath h a b c d hbal r).2) := by
  unfold typeIIShiftedBentHighest
  rw [standardBentPairHighest_at_target]
  exact standardBentPairHighest_eq_leftTree q hq hq1 d c (typeIIBentSourceIndex a b c d r)
    (a+h) (b+h) (typeIIBentTargetIndex h a b c d r)
    ((typeIIBentSource_label a b c d hbal r).trans (typeIIBentTarget_label h a b c d r).symm)
    (typeIIShiftedLeftPath h a b c d hbal r).2 rfl

end AMSPhysical
#print axioms AMSPhysical.typeIIShiftedBentHighest_eq_leftTree
