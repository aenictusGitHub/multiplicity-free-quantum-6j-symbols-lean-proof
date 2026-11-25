import QuantumTypeIICreationCoordinates
import NormalizedBasisOperator

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000
noncomputable section
namespace AMSPhysical

/-- Exact actual unit-basis cup coefficients in arbitrary rank reduce to
the rank-two raw coefficient times the actual positive square-root norm
ratio. This does not assert the remaining AMS shifted-channel equality. -/
theorem physicalTypeIIHighestRightCreation_unit_coordinate (q:ℝ) (hq:0<q) (hq1:q≠1)
    (n:ℕ) (hn:0<n) (a b c d:ℕ) (hbal:a+b=c+d)
    (r:TypeIICommonIndex a b c d) (s:TypeIICommonIndex a (b+1) (c+1) d) :
    (physicalTypeIILeftBasis q hq hq1 n hn a (b+1) (c+1) d (by omega)).repr
      (physicalTypeIIHighestRightCreation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d
        (physicalTypeIILeftCoupling q hq hq1 n hn a b c d hbal r)) s=
    (Real.sqrt (physicalTypeIILeftHighestNormSq q hq hq1 n hn a b c d hbal r))⁻¹*
      Real.sqrt (physicalTypeIILeftHighestNormSq q hq hq1 n hn a (b+1) (c+1) d (by omega) s)*
      (physicalTypeIILeftRawBasis q hq hq1 1 (by omega) a (b+1) (c+1) d (by omega)).repr
        (physicalTypeIIHighestRightCreation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 a b c d
          (physicalTypeIILeftHighest q hq hq1 1 (by omega) a b c d hbal r)) s := by
  have he:=unitsSMul_operator_coordinate
    (physicalTypeIILeftBasis q hq hq1 n hn a b c d hbal)
    (physicalTypeIILeftBasis q hq hq1 n hn a (b+1) (c+1) d (by omega))
    (fun r=>Units.mk0 (Real.sqrt (physicalTypeIILeftHighestNormSq q hq hq1 n hn a b c d hbal r))
      (ne_of_gt (Real.sqrt_pos.mpr (physicalTypeIILeftHighest_norm_pos q hq hq1 n hn a b c d hbal r))))
    (fun s=>Units.mk0 (Real.sqrt (physicalTypeIILeftHighestNormSq q hq hq1 n hn a (b+1) (c+1) d (by omega) s))
      (ne_of_gt (Real.sqrt_pos.mpr (physicalTypeIILeftHighest_norm_pos q hq hq1 n hn a (b+1) (c+1) d (by omega) s))))
    (physicalTypeIIHighestRightCreation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d) r s
  change _=_*(physicalTypeIILeftRawBasis q hq hq1 n hn a (b+1) (c+1) d (by omega)).repr
    (physicalTypeIIHighestRightCreation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d
      (physicalTypeIILeftRawBasis q hq hq1 n hn a b c d hbal r)) s at he
  rw [physicalTypeIILeftRawBasis_apply,physicalTypeIILeftBasis_apply,physicalTypeIIHighestRightCreation_raw_coordinate] at he
  exact he

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIIHighestRightCreation_unit_coordinate
