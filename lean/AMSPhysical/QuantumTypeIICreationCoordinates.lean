import QuantumTypeIICreationBoundary

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000
noncomputable section
namespace AMSPhysical

theorem physicalTypeIIUnshiftedBoundaryEquiv_repr (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ) (hbal:a+b=c+d)
    (v:physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d) :
    (physicalTypeIILeftRawBasis q hq hq1 1 (by omega) a b c d hbal).repr
      (physicalTypeIIUnshiftedBoundaryEquiv q hq hq1 n hn a b c d hbal v)=
      (physicalTypeIILeftRawBasis q hq hq1 n hn a b c d hbal).repr v := by
  unfold physicalTypeIIUnshiftedBoundaryEquiv
  simp only [LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply]

/-- Every matrix coefficient of ACTUAL physical cup creation in the
independent complete RAW two-row left bases is rank independent. All
indices and changing-degree boundary cases are included. -/
theorem physicalTypeIIHighestRightCreation_raw_coordinate (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ) (hbal:a+b=c+d)
    (r:TypeIICommonIndex a b c d) (s:TypeIICommonIndex a (b+1) (c+1) d) :
    (physicalTypeIILeftRawBasis q hq hq1 n hn a (b+1) (c+1) d (by omega)).repr
      (physicalTypeIIHighestRightCreation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d
        (physicalTypeIILeftHighest q hq hq1 n hn a b c d hbal r)) s=
    (physicalTypeIILeftRawBasis q hq hq1 1 (by omega) a (b+1) (c+1) d (by omega)).repr
      (physicalTypeIIHighestRightCreation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 a b c d
        (physicalTypeIILeftHighest q hq hq1 1 (by omega) a b c d hbal r)) s := by
  rw [← physicalTypeIIUnshiftedBoundaryEquiv_repr q hq hq1 n hn a (b+1) (c+1) d (by omega)]
  rw [physicalTypeIIUnshiftedBoundaryEquiv_right_creation,physicalTypeIIUnshiftedBoundaryEquiv_highest]

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIIHighestRightCreation_raw_coordinate
