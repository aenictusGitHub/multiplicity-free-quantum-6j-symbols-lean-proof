import TypeIIShiftedUnitCoordinates
import TypeIIShiftedCoordinateSpan

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

theorem typeIIShiftedUnitBoundaryMap_mem_span (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d)
    (v:physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a b c d):
    typeIIShiftedUnitBoundaryMap q hq hq1 h a b c d hbal v∈
      typeIIShiftedBentSpan q hq hq1 h a b c d hbal := by
  rw [← (physicalTypeIILeftBasis q hq hq1 (h+1) (by omega) a b c d hbal).sum_repr v]
  simp only [map_sum,map_smul]
  apply Submodule.sum_mem
  intro r hr
  apply Submodule.smul_mem
  rw [physicalTypeIILeftBasis_apply]
  have hn:=ne_of_gt (typeIIShiftedBendingAbs_pos q hq h a b c d hbal r)
  have he:typeIIShiftedUnitBoundaryMap q hq hq1 h a b c d hbal
      (physicalTypeIILeftCoupling q hq hq1 (h+1) (by omega) a b c d hbal r)=
      (typeIIShiftedBendingAbs q h a b c d hbal r)⁻¹ •
        typeIIShiftedBentHighest q hq hq1 h a b c d hbal r := by
    rw [← typeIIShiftedUnitBoundaryMap_left q hq hq1 h a b c d hbal r,
      smul_smul,inv_mul_cancel₀ hn,one_smul]
  rw [he]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨r,rfl⟩)

/-- The previously proved selected-coordinate injectivity applies to the
ENTIRE independently defined standard highest space at the AMS shift. -/
theorem typeIIShiftedHighest_boundary_mem_span (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d)
    (v:standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (a+h) (b+h) c d):
    standardTypeIIBoundaryEquiv (a+h) (b+h) c v.val∈
      typeIIShiftedBentSpan q hq hq1 h a b c d hbal := by
  have he:=typeIIShiftedUnitBoundaryMap_mem_span q hq hq1 h a b c d hbal
    ((typeIIShiftedUnitEquiv q hq hq1 h a b c d hbal).symm v)
  simpa only [typeIIShiftedUnitBoundaryMap,LinearMap.comp_apply,Submodule.subtype_apply,
    LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply] using he

theorem typeIIShiftedHighest_coordinate_ext (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d)
    (v w:standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (a+h) (b+h) c d)
    (hc:∀ k:TypeIICommonIndex a b c d,
      typeIIShiftedSelectedCoordinate h a b c d k (standardTypeIIBoundaryEquiv (a+h) (b+h) c v.val)=
      typeIIShiftedSelectedCoordinate h a b c d k (standardTypeIIBoundaryEquiv (a+h) (b+h) c w.val)):
    v=w := by
  apply Subtype.ext
  apply (standardTypeIIBoundaryEquiv (a+h) (b+h) c).injective
  exact typeIIShiftedBentSpan_coordinate_ext q hq hq1 h a b c d hbal _ _
    (typeIIShiftedHighest_boundary_mem_span q hq hq1 h a b c d hbal v)
    (typeIIShiftedHighest_boundary_mem_span q hq hq1 h a b c d hbal w) hc

end AMSPhysical
#print axioms AMSPhysical.typeIIShiftedHighest_coordinate_ext
