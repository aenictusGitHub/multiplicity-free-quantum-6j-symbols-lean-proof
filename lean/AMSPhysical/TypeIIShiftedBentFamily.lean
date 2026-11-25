import StandardBentPairHighest
import QuantumTypeIILeftPair

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def typeIIBentSourceIndex (a b c d:ℕ) (r:TypeIICommonIndex a b c d):Fin (min d c+1):=
  ⟨r.val,by have h:=r.isLt;omega⟩
def typeIIBentTargetIndex (h a b c d:ℕ) (r:TypeIICommonIndex a b c d):Fin (min (a+h) (b+h)+1):=
  ⟨r.val+h,by have hr:=r.isLt;omega⟩
def typeIIBentLabel (a b c d:ℕ) (r:TypeIICommonIndex a b c d):ℕ:=a+b-2*r.val

theorem typeIIBentSource_label (a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d):
    coupledLabel d c (typeIIBentSourceIndex a b c d r)=typeIIBentLabel a b c d r := by
  change d+c-2*r.val=a+b-2*r.val
  omega

theorem typeIIBentTarget_label (h a b c d:ℕ) (r:TypeIICommonIndex a b c d):
    coupledLabel (a+h) (b+h) (typeIIBentTargetIndex h a b c d r)=typeIIBentLabel a b c d r := by
  change a+h+(b+h)-2*(r.val+h)=a+b-2*r.val
  omega

/-- Independent standard bent family at the AMS determinant background.
The source contraction is r, while the target contraction is r+h. -/
def typeIIShiftedBentHighest (q:ℝ) (hq:0<q) (hq1:q≠1) (h a b c d:ℕ) (hbal:a+b=c+d)
    (r:TypeIICommonIndex a b c d) :=
  standardBentPairHighest q hq hq1 d c (typeIIBentSourceIndex a b c d r)
    (a+h) (b+h) (typeIIBentTargetIndex h a b c d r) (typeIIBentLabel a b c d r)
    (typeIIBentSource_label a b c d hbal r) (typeIIBentTarget_label h a b c d r)

def typeIIShiftedLeadingCoefficient (q:ℝ) (h a b c d:ℕ) (r:TypeIICommonIndex a b c d):ℝ:=
  (-1:ℝ)^(r.val:ℤ)/(Real.sqrt (quantumHighestNorm q d c (typeIIBentSourceIndex a b c d r))*
    Real.sqrt (quantumHighestNorm q (a+h) (b+h) (typeIIBentTargetIndex h a b c d r)))

theorem typeIIShiftedLeadingCoefficient_ne_zero (q:ℝ) (hq:0<q) (h a b c d:ℕ)
    (r:TypeIICommonIndex a b c d):typeIIShiftedLeadingCoefficient q h a b c d r≠0 := by
  apply div_ne_zero
  · exact zpow_ne_zero _ (by norm_num : (-1:ℝ)≠0)
  · exact mul_ne_zero
      (ne_of_gt (Real.sqrt_pos.mpr (quantumHighestNorm_pos q hq d c _)))
      (ne_of_gt (Real.sqrt_pos.mpr (quantumHighestNorm_pos q hq (a+h) (b+h) _)))

/-- Literal selected coordinate on the shifted first-two-coordinate space.
It is linear and defined without a candidate overlap. -/
def typeIIShiftedSelectedCoordinate (h a b c d:ℕ) (k:TypeIICommonIndex a b c d):
    (finiteWeightSpace (K:=ℝ) (a+h) ⊗[ℝ]
      (finiteWeightSpace (K:=ℝ) (b+h) ⊗[ℝ] finiteWeightSpace (K:=ℝ) c)) →ₗ[ℝ] ℝ :=
  (Finsupp.lapply (0,(⟨k.val+h,by have hk:=k.isLt;omega⟩,⟨k.val,by have hk:=k.isLt;omega⟩))).comp
    ((standardWeightBasis (K:=ℝ) (a+h)).tensorProduct
      ((standardWeightBasis (K:=ℝ) (b+h)).tensorProduct (standardWeightBasis (K:=ℝ) c))).repr.toLinearMap

theorem typeIIShiftedSelectedCoordinate_below (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (r k:TypeIICommonIndex a b c d) (hk:k.val<r.val):
    typeIIShiftedSelectedCoordinate h a b c d k (typeIIShiftedBentHighest q hq hq1 h a b c d hbal r)=0 :=
  standardBentPairHighest_below q hq hq1 d c (typeIIBentSourceIndex a b c d r)
    (a+h) (b+h) (typeIIBentTargetIndex h a b c d r) (typeIIBentLabel a b c d r)
    _ _ 0 ⟨k.val+h,by have hb:=k.isLt;omega⟩ ⟨k.val,by have hb:=k.isLt;omega⟩ hk

theorem typeIIShiftedSelectedCoordinate_leading (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d):
    typeIIShiftedSelectedCoordinate h a b c d r (typeIIShiftedBentHighest q hq hq1 h a b c d hbal r)=
      typeIIShiftedLeadingCoefficient q h a b c d r :=
  standardBentPairHighest_leading q hq hq1 d c (typeIIBentSourceIndex a b c d r)
    (a+h) (b+h) (typeIIBentTargetIndex h a b c d r) (typeIIBentLabel a b c d r)
    _ _ ⟨r.val,by have hr:=r.isLt;omega⟩ ⟨r.val+h,by have hr:=r.isLt;omega⟩ rfl rfl

end AMSPhysical
#print axioms AMSPhysical.typeIIShiftedSelectedCoordinate_leading
