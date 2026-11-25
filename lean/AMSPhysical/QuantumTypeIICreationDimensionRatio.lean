import QuantumTypeIINormalizedCreation
import QuantumTypeIILeftNormClosed

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000
noncomputable section
namespace AMSPhysical

theorem positive_common_denominator_sqrt_ratio (A B S:ℝ) (hA:0<A) (hB:0<B) (hS:0<S) :
    (Real.sqrt (A/S))⁻¹*Real.sqrt (B/S)=Real.sqrt (B/A) := by
  rw [Real.sqrt_div hA.le,Real.sqrt_div hB.le,Real.sqrt_div hB.le]
  have hs:=ne_of_gt (Real.sqrt_pos.mpr hS)
  have ha:=ne_of_gt (Real.sqrt_pos.mpr hA)
  field_simp [hs,ha]

/-- The common output quantum dimension cancels EXACTLY in every actual
unit Type-II creation coefficient. Only the ratio of independently proved
actual two-row pivotal dimensions remains; the raw coefficient is rank two. -/
theorem physicalTypeIIHighestRightCreation_dimension_ratio (q:ℝ) (hq:0<q) (hq1:q≠1)
    (n:ℕ) (hn:0<n) (a b c d:ℕ) (hbal:a+b=c+d)
    (r:TypeIICommonIndex a b c d) (s:TypeIICommonIndex a (b+1) (c+1) d) :
    (physicalTypeIILeftBasis q hq hq1 n hn a (b+1) (c+1) d (by omega)).repr
      (physicalTypeIIHighestRightCreation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d
        (physicalTypeIILeftCoupling q hq hq1 n hn a b c d hbal r)) s=
    Real.sqrt (twoRowIrrepQuantumDimension q hq hq1 n hn ((a-s.val)+(b+1-s.val)) s.val/
      twoRowIrrepQuantumDimension q hq hq1 n hn ((a-r.val)+(b-r.val)) r.val)*
      (physicalTypeIILeftRawBasis q hq hq1 1 (by omega) a (b+1) (c+1) d (by omega)).repr
        (physicalTypeIIHighestRightCreation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 a b c d
          (physicalTypeIILeftHighest q hq hq1 1 (by omega) a b c d hbal r)) s := by
  rw [physicalTypeIIHighestRightCreation_unit_coordinate,
    physicalTypeIILeftHighestNormSq_closed q hq hq1 n hn a b c d hbal r,
    physicalTypeIILeftHighestNormSq_closed q hq hq1 n hn a (b+1) (c+1) d (by omega) s]
  rw [positive_common_denominator_sqrt_ratio _ _ _
    (twoRowIrrepQuantumDimension_pos q hq hq1 n hn _ _)
    (twoRowIrrepQuantumDimension_pos q hq hq1 n hn _ _)
    (show 0<symmetricQuantumDimension q n d from
      div_pos (qfactorial_pos q hq _) (mul_pos (qfactorial_pos q hq _) (qfactorial_pos q hq _)))]

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIIHighestRightCreation_dimension_ratio
