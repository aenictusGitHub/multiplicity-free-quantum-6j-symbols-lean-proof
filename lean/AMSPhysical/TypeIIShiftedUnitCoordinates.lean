import TypeIIShiftedUnitEquivalence
import TypeIIShiftedUniversalNormalization
import QuantumTypeIIStandardBoundaryIdentification

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def typeIIShiftedUnitBoundaryMap (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d):
    physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a b c d →ₗ[ℝ]
      (finiteWeightSpace (K:=ℝ) (a+h) ⊗[ℝ]
        (finiteWeightSpace (K:=ℝ) (b+h) ⊗[ℝ] finiteWeightSpace (K:=ℝ) c)):=
  (standardTypeIIBoundaryEquiv (a+h) (b+h) c).toLinearMap.comp
    ((standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      (a+h) (b+h) c d).subtype.comp
        (typeIIShiftedUnitEquiv q hq hq1 h a b c d hbal).toLinearMap)

theorem typeIIShiftedUnitBoundaryMap_left (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d):
    typeIIShiftedBendingAbs q h a b c d hbal r •
      typeIIShiftedUnitBoundaryMap q hq hq1 h a b c d hbal
        (physicalTypeIILeftCoupling q hq hq1 (h+1) (by omega) a b c d hbal r)=
      typeIIShiftedBentHighest q hq hq1 h a b c d hbal r := by
  unfold typeIIShiftedUnitBoundaryMap
  simp only [LinearMap.comp_apply,Submodule.subtype_apply,LinearEquiv.coe_coe]
  rw [typeIIShiftedUnitEquiv_left,typeIIShiftedBentHighest_eq_signed_leftTree]
  simp only [Submodule.coe_smul_of_tower,map_smul,smul_smul]
  change (typeIIShiftedBendingAbs q h a b c d hbal r*((-1:ℝ)^r.val)) • _=
    (((-1:ℝ)^r.val)*typeIIShiftedBendingAbs q h a b c d hbal r) • _
  rw [mul_comm]
  rfl

theorem typeIIShiftedUnitBoundaryMap_left_coordinate (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (r k:TypeIICommonIndex a b c d):
    typeIIShiftedSelectedCoordinate h a b c d k
      (typeIIShiftedUnitBoundaryMap q hq hq1 h a b c d hbal
        (physicalTypeIILeftCoupling q hq hq1 (h+1) (by omega) a b c d hbal r))=
      (Real.sqrt (typeIIDeterminantMetricScale q h a b d))⁻¹*q^(-(h:ℤ)*(k.val:ℤ))*
        typeIIShiftedSelectedCoordinate 0 a b c d k
          (twoVertexTripleProjection (h+1) (by omega) a b c
            (physicalTypeIILeftCoupling q hq hq1 (h+1) (by omega) a b c d hbal r).val) := by
  have hb:=congrArg (typeIIShiftedSelectedCoordinate h a b c d k)
    (typeIIShiftedUnitBoundaryMap_left q hq hq1 h a b c d hbal r)
  simp only [map_smul,smul_eq_mul] at hb
  have hp:twoVertexTripleProjection (h+1) (by omega) a b c
      (physicalTypeIILeftCoupling q hq hq1 (h+1) (by omega) a b c d hbal r).val=
      (Real.sqrt (physicalTypeIILeftHighestNormSq q hq hq1 (h+1) (by omega) a b c d hbal r))⁻¹ •
        typeIIShiftedBentHighest q hq hq1 0 a b c d hbal r:=by
    unfold physicalTypeIILeftCoupling
    simp only [Submodule.coe_smul_of_tower,map_smul,physicalTypeIILeftHighest_boundary_standard]
  rw [hp,map_smul,smul_eq_mul]
  have ht:=typeIIShiftedBent_coordinate_transport q hq hq1 h a b c d hbal r k
  rw [← hb] at ht
  have hu:=typeIIShiftedUniversalNormalization q hq hq1 h a b c d hbal r
  have hC:Real.sqrt (typeIIDeterminantMetricScale q h a b d)≠0:=
    ne_of_gt (Real.sqrt_pos.mpr (typeIIDeterminantMetricScale_pos q hq h a b d))
  have hN:Real.sqrt (physicalTypeIILeftHighestNormSq q hq hq1 (h+1) (by omega) a b c d hbal r)≠0:=
    ne_of_gt (Real.sqrt_pos.mpr (physicalTypeIILeftHighest_norm_pos q hq hq1 (h+1) (by omega) a b c d hbal r))
  apply (mul_left_cancel₀ (mul_ne_zero hC hN))
  calc
    _=(typeIIShiftedBentScale q h a b c d r*typeIIShiftedBendingAbs q h a b c d hbal r)*
        typeIIShiftedSelectedCoordinate h a b c d k
          (typeIIShiftedUnitBoundaryMap q hq hq1 h a b c d hbal
            (physicalTypeIILeftCoupling q hq hq1 (h+1) (by omega) a b c d hbal r)):=by rw [hu]
    _=q^(-(h:ℤ)*(k.val:ℤ))*typeIIShiftedSelectedCoordinate 0 a b c d k
        (typeIIShiftedBentHighest q hq hq1 0 a b c d hbal r):=by rw [mul_assoc];exact ht
    _=_:=by field_simp [hC,hN]

theorem typeIIShiftedUnitBoundaryMap_coordinate (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d)
    (v:physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a b c d)
    (k:TypeIICommonIndex a b c d):
    typeIIShiftedSelectedCoordinate h a b c d k
      (typeIIShiftedUnitBoundaryMap q hq hq1 h a b c d hbal v)=
      (Real.sqrt (typeIIDeterminantMetricScale q h a b d))⁻¹*q^(-(h:ℤ)*(k.val:ℤ))*
        typeIIShiftedSelectedCoordinate 0 a b c d k
          (twoVertexTripleProjection (h+1) (by omega) a b c v.val) := by
  let V:=physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a b c d
  letI:AddCommGroup V:=inferInstance
  letI:Module ℝ V:=inferInstance
  have he:(typeIIShiftedSelectedCoordinate h a b c d k).comp
        (typeIIShiftedUnitBoundaryMap q hq hq1 h a b c d hbal)=
      ((Real.sqrt (typeIIDeterminantMetricScale q h a b d))⁻¹*q^(-(h:ℤ)*(k.val:ℤ))) •
        ((typeIIShiftedSelectedCoordinate 0 a b c d k).comp
          (physicalTypeIIHighestBoundaryMap q hq hq1 (h+1) (by omega) a b c d)):=by
    apply (physicalTypeIILeftBasis q hq hq1 (h+1) (by omega) a b c d hbal).ext
    intro r
    rw [physicalTypeIILeftBasis_apply]
    exact typeIIShiftedUnitBoundaryMap_left_coordinate q hq hq1 h a b c d hbal r k
  exact DFunLike.congr_fun he v

end AMSPhysical
#print axioms AMSPhysical.typeIIShiftedUnitBoundaryMap_coordinate
