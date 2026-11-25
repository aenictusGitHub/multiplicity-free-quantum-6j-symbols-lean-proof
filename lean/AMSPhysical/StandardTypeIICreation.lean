import RankTwoTypeIIHighestEquivalence
import RankTwoTypeIIBoundary
import QuantumTypeIICreationBoundary

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

/-- Actual rank-two mixed cup creation on the independent standard highest
space, using the proved representation equivalence. -/
def standardTypeIIHighestRightCreation (q:ℝ) (hq:0<q) (hq1:q≠1) (a b c d:ℕ):
    standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) a b c d →ₗ[ℝ]
      standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) a (b+1) (c+1) d :=
  (rankTwoTypeIIHighestEquiv q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) a (b+1) (c+1) d).symm.toLinearMap.comp
    ((physicalTypeIIHighestRightCreation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 a b c d).comp
      (rankTwoTypeIIHighestEquiv q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) a b c d).toLinearMap)

theorem standardTypeIIHighestRightCreation_physical (q:ℝ) (hq:0<q) (hq1:q≠1) (a b c d:ℕ)
    (v:standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) a b c d):
    rankTwoTypeIIHighestEquiv q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) a (b+1) (c+1) d
      (standardTypeIIHighestRightCreation q hq hq1 a b c d v)=
      physicalTypeIIHighestRightCreation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 a b c d
        (rankTwoTypeIIHighestEquiv q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) a b c d v) := by
  simp only [standardTypeIIHighestRightCreation,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  rfl

theorem standardTypeIIHighestRightCreation_boundary (q:ℝ) (hq:0<q) (hq1:q≠1) (a b c d:ℕ)
    (v:standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) a b c d):
    standardTypeIIBoundaryEquiv a (b+1) (c+1) (standardTypeIIHighestRightCreation q hq hq1 a b c d v).val=
      typeIIStandardRightCreation q a b c (standardTypeIIBoundaryEquiv a b c v.val) := by
  rw [← rankTwoTypeIITripleEquiv_boundary]
  have he:=congrArg Subtype.val (standardTypeIIHighestRightCreation_physical q hq hq1 a b c d v)
  rw [rankTwoTypeIIHighestEquiv_literal] at he
  rw [he]
  change twoVertexTripleProjection 1 (by omega) a (b+1) (c+1)
      (physicalTypeIIRightCreation q 1 a b c
        (rankTwoTypeIIHighestEquiv q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) a b c d v).val)=_
  rw [physicalTypeIIRightCreation_boundary,rankTwoTypeIIHighestEquiv_literal,rankTwoTypeIITripleEquiv_boundary]

end AMSPhysical
#print axioms AMSPhysical.standardTypeIIHighestRightCreation_boundary
