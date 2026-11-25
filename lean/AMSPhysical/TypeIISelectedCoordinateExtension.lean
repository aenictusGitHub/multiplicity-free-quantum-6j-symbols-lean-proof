import TypeIIShiftedUnitCoordinates
import TypeIIShiftedCoordinateSpan
import StandardBoundaryCreationCoordinate

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

theorem standardBoundaryCoordinate_eq_typeIISelected (h a b c d:ℕ)
    (k:TypeIICommonIndex a b c d):
    standardBoundaryCoordinate (a+h) (b+h) c (k.val+h) k.val=
      typeIIShiftedSelectedCoordinate h a b c d k := by
  have hk:=k.isLt
  rw [standardBoundaryCoordinate,dif_pos (by omega),dif_pos (by omega)]
  rfl

theorem standardBoundaryCoordinate_eq_typeIISelectedNat (h a b c d k:ℕ)
    (ha:k≤a) (hd:k≤d):
    standardBoundaryCoordinate (a+h) (b+h) c (k+h) k=
      typeIIShiftedSelectedCoordinateNat h a b c d k := by
  unfold typeIIShiftedSelectedCoordinateNat
  split_ifs with hk
  · exact standardBoundaryCoordinate_eq_typeIISelected h a b c d ⟨k,hk⟩
  · unfold standardBoundaryCoordinate
    split_ifs with hb hc
    · omega
    · rfl
    · rfl

/-- The universal coordinate formula includes the finite-range zero terms
needed for adjacent creation, without assuming a generic interior channel. -/
theorem typeIIShiftedUnitBoundaryMap_extended_coordinate (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d)
    (v:physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a b c d)
    (k:ℕ) (ha:k≤a) (hd:k≤d):
    standardBoundaryCoordinate (a+h) (b+h) c (k+h) k
      (typeIIShiftedUnitBoundaryMap q hq hq1 h a b c d hbal v)=
      (Real.sqrt (typeIIDeterminantMetricScale q h a b d))⁻¹*q^(-(h:ℤ)*(k:ℤ))*
        standardBoundaryCoordinate a b c k k
          (twoVertexTripleProjection (h+1) (by omega) a b c v.val) := by
  rw [standardBoundaryCoordinate_eq_typeIISelectedNat h a b c d k ha hd]
  have he:=standardBoundaryCoordinate_eq_typeIISelectedNat 0 a b c d k ha hd
  simp only [Nat.add_zero] at he
  rw [he]
  unfold typeIIShiftedSelectedCoordinateNat
  split_ifs with hk
  · exact typeIIShiftedUnitBoundaryMap_coordinate q hq hq1 h a b c d hbal v ⟨k,hk⟩
  · simp only [LinearMap.zero_apply,mul_zero]

end AMSPhysical
#print axioms AMSPhysical.typeIIShiftedUnitBoundaryMap_extended_coordinate
