import TypeIIShiftedCompleteCoordinates
import TypeIISelectedCoordinateExtension
import TypeIIStandardShiftedCreation
import QuantumDeterminantDifference
import TypeIICreationMetricRatio

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

/-- The full-space isometry intertwines the ACTUAL physical cup creation
with the independently constructed shifted rank-two creation, with the
universal positive degree-step scalar. -/
theorem typeIIShiftedUnitEquiv_creation (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d)
    (v:physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a b c d):
    typeIIShiftedUnitEquiv q hq hq1 h a (b+1) (c+1) d (by omega)
      (physicalTypeIIHighestRightCreation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a b c d v)=
      typeIICreationIsometryScalar q h a b d •
        standardTypeIIShiftedRightCreation q hq hq1 h a b c d
          (typeIIShiftedUnitEquiv q hq hq1 h a b c d hbal v) := by
  apply typeIIShiftedHighest_coordinate_ext q hq hq1 h a (b+1) (c+1) d (by omega)
  intro k
  have hki:=k.isLt
  rw [← standardBoundaryCoordinate_eq_typeIISelected h a (b+1) (c+1) d k]
  simp only [Submodule.coe_smul_of_tower,map_smul,smul_eq_mul]
  let f:ℕ → ℝ:=fun j=>standardBoundaryCoordinate a b c j j
    (twoVertexTripleProjection (h+1) (by omega) a b c v.val)
  let g:ℕ → ℝ:=fun j=>standardBoundaryCoordinate (a+h) (b+h) c (j+h) j
    (typeIIShiftedUnitBoundaryMap q hq hq1 h a b c d hbal v)
  let α:ℝ:=(Real.sqrt (typeIIDeterminantMetricScale q h a b d))⁻¹
  let β:ℝ:=(Real.sqrt (typeIIDeterminantMetricScale q h a (b+1) d))⁻¹
  have hg:g k.val=α*q^(-(h:ℤ)*(k.val:ℤ))*f k.val:=
    typeIIShiftedUnitBoundaryMap_extended_coordinate q hq hq1 h a b c d hbal v k.val (by omega) (by omega)
  have hgp:k.val≠0 → g (k.val-1)=α*q^(-(h:ℤ)*((k.val-1:ℕ):ℤ))*f (k.val-1):=by
    intro hk
    exact typeIIShiftedUnitBoundaryMap_extended_coordinate q hq hq1 h a b c d hbal v (k.val-1) (by omega) (by omega)
  have hd:=quantumDeterminantDifference q hq h b c k.val α f g hg hgp
  have h0:=standardBoundaryCoordinate_typeII_creation q hq 0 a b c k.val
    (twoVertexTripleProjection (h+1) (by omega) a b c v.val)
  simp only [Nat.add_zero,Nat.cast_zero,neg_zero,zero_sub,add_zero] at h0
  have hright:standardBoundaryCoordinate (a+h) (b+1+h) (c+1) (k.val+h) k.val
      (standardTypeIIBoundaryEquiv (a+h) (b+1+h) (c+1)
        (standardTypeIIShiftedRightCreation q hq hq1 h a b c d
          (typeIIShiftedUnitEquiv q hq hq1 h a b c d hbal v)).val)=
      α*q^(-(h:ℤ)*(k.val:ℤ))*standardBoundaryCoordinate a (b+1) (c+1) k.val k.val
        (typeIIStandardRightCreation q a b c
          (twoVertexTripleProjection (h+1) (by omega) a b c v.val)):=by
    rw [standardTypeIIShiftedRightCreation_boundary_coordinate,standardBoundaryCoordinate_typeII_creation q hq]
    exact hd.trans (congrArg (fun x:ℝ=>α*q^(-(h:ℤ)*(k.val:ℤ))*x) h0.symm)
  have hleft:=typeIIShiftedUnitBoundaryMap_extended_coordinate q hq hq1 h a (b+1) (c+1) d (by omega)
    (physicalTypeIIHighestRightCreation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a b c d v)
    k.val (by omega) (by omega)
  change standardBoundaryCoordinate (a+h) (b+1+h) (c+1) (k.val+h) k.val
      (standardTypeIIBoundaryEquiv (a+h) (b+1+h) (c+1)
        (typeIIShiftedUnitEquiv q hq hq1 h a (b+1) (c+1) d _
          (physicalTypeIIHighestRightCreation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a b c d v)).val)=
    β*q^(-(h:ℤ)*(k.val:ℤ))*standardBoundaryCoordinate a (b+1) (c+1) k.val k.val
      (twoVertexTripleProjection (h+1) (by omega) a (b+1) (c+1)
        (physicalTypeIIRightCreation q (h+1) a b c v.val)) at hleft
  rw [physicalTypeIIRightCreation_boundary] at hleft
  have hs:β=typeIICreationIsometryScalar q h a b d*α:=by
    dsimp only [α,β,typeIICreationIsometryScalar]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr (typeIIDeterminantMetricScale_pos q hq h a b d)),
      ne_of_gt (Real.sqrt_pos.mpr (typeIIDeterminantMetricScale_pos q hq h a (b+1) d))]
  rw [hleft,hright,hs]
  ring

end AMSPhysical
#print axioms AMSPhysical.typeIIShiftedUnitEquiv_creation
