import TypeIIShiftedBentLeftTree
import QuantumCouplingBentNorm

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

def typeIIShiftedBendingAbs (q:ℝ) (h a b c d:ℕ) (hbal:a+b=c+d)
    (r:TypeIICommonIndex a b c d):ℝ:=
  Real.sqrt (quantumHighestNorm q
    (coupledLabel (a+h) (b+h) (typeIIShiftedLeftPath h a b c d hbal r).1) c
    (typeIIShiftedLeftPath h a b c d hbal r).2)/
      Real.sqrt (quantumHighestNorm q d c (typeIIBentSourceIndex a b c d r))

theorem typeIIShiftedBendingAbs_pos (q:ℝ) (hq:0<q) (h a b c d:ℕ) (hbal:a+b=c+d)
    (r:TypeIICommonIndex a b c d):0<typeIIShiftedBendingAbs q h a b c d hbal r :=
  div_pos (Real.sqrt_pos.mpr (quantumHighestNorm_pos q hq _ _ _))
    (Real.sqrt_pos.mpr (quantumHighestNorm_pos q hq _ _ _))

theorem typeIIShiftedBendingAbs_sq (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d):
    (typeIIShiftedBendingAbs q h a b c d hbal r)^2=
      qnum q (typeIIBentLabel a b c d r+1)/qnum q (d+1) := by
  unfold typeIIShiftedBendingAbs
  rw [div_pow,Real.sq_sqrt (quantumHighestNorm_pos q hq _ _ _).le,
    Real.sq_sqrt (quantumHighestNorm_pos q hq _ _ _).le]
  have hL:coupledLabel d c (typeIIBentSourceIndex a b c d r)=
      coupledLabel (a+h) (b+h) (typeIIShiftedLeftPath h a b c d hbal r).1:=
    (typeIIBentSource_label a b c d hbal r).trans (typeIIBentTarget_label h a b c d r).symm
  have ht:coupledLabel (a+h) (b+h) (typeIIShiftedLeftPath h a b c d hbal r).1=typeIIBentLabel a b c d r:=
    typeIIBentTarget_label h a b c d r
  rw [quantumHighestNorm_bent q hq hq1 d c (typeIIBentSourceIndex a b c d r) _ hL _ rfl,
    ht,
    ← qnum_eq_qInteger q hq hq1,← qnum_eq_qInteger q hq hq1]
  field_simp [ne_of_gt (quantumHighestNorm_pos q hq d c (typeIIBentSourceIndex a b c d r))]

theorem typeIIShiftedBentHighest_eq_signed_leftTree (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d):
    typeIIShiftedBentHighest q hq hq1 h a b c d hbal r=
      ((-1:ℝ)^r.val*typeIIShiftedBendingAbs q h a b c d hbal r) •
        standardTypeIIBoundaryEquiv (a+h) (b+h) c
          (quantumLeftTreeHighest q hq hq1 (a+h) (b+h) c
            (typeIIShiftedLeftPath h a b c d hbal r).1
            (typeIIShiftedLeftPath h a b c d hbal r).2) := by
  rw [typeIIShiftedBentHighest_eq_leftTree]
  simp only [zpow_natCast,typeIIShiftedBendingAbs]
  congr 1
  ring

end AMSPhysical
#print axioms AMSPhysical.typeIIShiftedBendingAbs_sq
