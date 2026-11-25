import StandardTypeIICreation
import StandardBoundaryCreationCoordinate

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

def standardHighestSecondDegreeEquiv (q:ℝ) (hq:q≠0) (hD:q-q⁻¹≠0)
    (a b b' c d:ℕ) (hb:b=b'):
    standardTypeAHighestMultiplicity q hq hD a b c d ≃ₗ[ℝ]
      standardTypeAHighestMultiplicity q hq hD a b' c d := by
  subst b'
  exact LinearEquiv.refl ℝ _

theorem standardHighestSecondDegreeEquiv_boundary_coordinate (q:ℝ) (hq:q≠0) (hD:q-q⁻¹≠0)
    (a b b' c d j k:ℕ) (hb:b=b')
    (v:standardTypeAHighestMultiplicity q hq hD a b c d):
    standardBoundaryCoordinate a b' c j k
      (standardTypeIIBoundaryEquiv a b' c (standardHighestSecondDegreeEquiv q hq hD a b b' c d hb v).val)=
      standardBoundaryCoordinate a b c j k (standardTypeIIBoundaryEquiv a b c v.val) := by
  subst b'
  rfl

def standardTypeIIShiftedRightCreation (q:ℝ) (hq:0<q) (hq1:q≠1) (h a b c d:ℕ):
    standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (a+h) (b+h) c d →ₗ[ℝ]
      standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (a+h) (b+1+h) (c+1) d :=
  (standardHighestSecondDegreeEquiv q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
    (a+h) (b+h+1) (b+1+h) (c+1) d (by omega)).toLinearMap.comp
    (standardTypeIIHighestRightCreation q hq hq1 (a+h) (b+h) c d)

theorem standardTypeIIShiftedRightCreation_boundary_coordinate (q:ℝ) (hq:0<q) (hq1:q≠1) (h a b c d k:ℕ)
    (v:standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (a+h) (b+h) c d):
    standardBoundaryCoordinate (a+h) (b+1+h) (c+1) (k+h) k
      (standardTypeIIBoundaryEquiv (a+h) (b+1+h) (c+1)
        (standardTypeIIShiftedRightCreation q hq hq1 h a b c d v).val)=
      standardBoundaryCoordinate (a+h) (b+h+1) (c+1) (k+h) k
        (typeIIStandardRightCreation q (a+h) (b+h) c
          (standardTypeIIBoundaryEquiv (a+h) (b+h) c v.val)) := by
  unfold standardTypeIIShiftedRightCreation
  rw [LinearMap.comp_apply]
  change standardBoundaryCoordinate (a+h) (b+1+h) (c+1) (k+h) k
    (standardTypeIIBoundaryEquiv (a+h) (b+1+h) (c+1)
      (standardHighestSecondDegreeEquiv q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
        (a+h) (b+h+1) (b+1+h) (c+1) d _
        (standardTypeIIHighestRightCreation q hq hq1 (a+h) (b+h) c d v)).val)=_
  rw [standardHighestSecondDegreeEquiv_boundary_coordinate,standardTypeIIHighestRightCreation_boundary]

end AMSPhysical
#print axioms AMSPhysical.standardTypeIIShiftedRightCreation_boundary_coordinate
