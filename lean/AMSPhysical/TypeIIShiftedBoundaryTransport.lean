import TypeIIShiftedBentFamily
import StandardClebschDeterminantShift

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def typeIIShiftedBentScale (q:ℝ) (h a b c d:ℕ) (r:TypeIICommonIndex a b c d):ℝ:=
  q^(-(h:ℤ)*(r.val:ℤ))*
    (Real.sqrt (quantumHighestNorm q (a+h) (b+h) (typeIIBentTargetIndex h a b c d r))/
      Real.sqrt (quantumHighestNorm q a b (typeIIBentTargetIndex 0 a b c d r)))

theorem typeIIShiftedBentScale_pos (q:ℝ) (hq:0<q) (h a b c d:ℕ) (r:TypeIICommonIndex a b c d):
    0<typeIIShiftedBentScale q h a b c d r :=
  mul_pos (zpow_pos hq _) (div_pos (Real.sqrt_pos.mpr (quantumHighestNorm_pos q hq (a+h) (b+h) _))
    (Real.sqrt_pos.mpr (quantumHighestNorm_pos q hq a b _)))

/-- Exact determinant-background coordinate transport, including all
admissible zero labels and both sides of the triangular boundary. This is
a scalar-coordinate identity for independently constructed actual bent
vectors; metric and full-space identifications are proved separately. -/
theorem typeIIShiftedBent_coordinate_transport (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (r k:TypeIICommonIndex a b c d):
    typeIIShiftedBentScale q h a b c d r*
      typeIIShiftedSelectedCoordinate h a b c d k (typeIIShiftedBentHighest q hq hq1 h a b c d hbal r)=
      q^(-(h:ℤ)*(k.val:ℤ))*
        typeIIShiftedSelectedCoordinate 0 a b c d k (typeIIShiftedBentHighest q hq hq1 0 a b c d hbal r) := by
  by_cases hkr:k.val<r.val
  · rw [typeIIShiftedSelectedCoordinate_below q hq hq1 h a b c d hbal r k hkr,
      typeIIShiftedSelectedCoordinate_below q hq hq1 0 a b c d hbal r k hkr,mul_zero,mul_zero]
  · have hri:=r.isLt
    have hki:=k.isLt
    let t:Fin (typeIIBentLabel a b c d r+1):=⟨k.val-r.val,by unfold typeIIBentLabel;omega⟩
    let z:Fin (c+1):=⟨k.val,by omega⟩
    let j:Fin (b+1):=⟨k.val,by omega⟩
    let rs:=typeIIBentSourceIndex a b c d r
    let rt:=typeIIBentTargetIndex 0 a b c d r
    let L:=typeIIBentLabel a b c d r
    let hs:=typeIIBentSource_label a b c d hbal r
    let ht:=typeIIBentTarget_label 0 a b c d r
    have hz:z.val=rs.val+t.val:=by change k.val=r.val+(k.val-r.val);omega
    have hj:j.val=rt.val+t.val:=by change k.val=r.val+0+(k.val-r.val);omega
    have heh:=standardBentPairHighest_coordinate q hq hq1 d c rs (a+h) (b+h)
      (typeIIBentTargetIndex h a b c d r) L hs (typeIIBentTarget_label h a b c d r)
      t z (standardWeightShiftIndex h b j) hz
    have he0:=standardBentPairHighest_coordinate q hq hq1 d c rs a b rt L hs ht t z j hz
    have heT:=standardClebsch_first_determinant_shift q hq hq1 h a b rt L ht t j hj
    let S:=((standardWeightBasis (K:=ℝ) d).tensorProduct (standardWeightBasis (K:=ℝ) c)).repr
      (standardClebschAtLabel q hq hq1 d c rs L hs (standardWeightBasis L t)) (0,z)
    let T:=((standardWeightBasis (K:=ℝ) a).tensorProduct (standardWeightBasis (K:=ℝ) b)).repr
      (standardClebschAtLabel q hq hq1 a b rt L ht (standardWeightBasis L t)) (0,j)
    let U:=((standardWeightBasis (K:=ℝ) (a+h)).tensorProduct (standardWeightBasis (K:=ℝ) (b+h))).repr
      (standardClebschAtLabel q hq hq1 (a+h) (b+h) (typeIIBentTargetIndex h a b c d r) L
        (typeIIBentTarget_label h a b c d r) (standardWeightBasis L t)) (0,standardWeightShiftIndex h b j)
    have hU:U=(Real.sqrt (quantumHighestNorm q a b rt)/
      Real.sqrt (quantumHighestNorm q (a+h) (b+h) (typeIIBentTargetIndex h a b c d r)))*
      q^(-(h:ℤ)*(t.val:ℤ))*T:=heT
    have hPow:q^(-(h:ℤ)*(r.val:ℤ))*q^(-(h:ℤ)*(t.val:ℤ))=q^(-(h:ℤ)*(k.val:ℤ)):=by
      rw [← zpow_add₀ (ne_of_gt hq)]
      congr 1
      have hh:(r.val:ℤ)+(t.val:ℤ)=(k.val:ℤ):=by dsimp only [t];omega
      linear_combination -(h:ℤ)*hh
    have hCancel:(Real.sqrt (quantumHighestNorm q (a+h) (b+h) (typeIIBentTargetIndex h a b c d r))/
        Real.sqrt (quantumHighestNorm q a b rt))*
        (Real.sqrt (quantumHighestNorm q a b rt)/
        Real.sqrt (quantumHighestNorm q (a+h) (b+h) (typeIIBentTargetIndex h a b c d r)))=1:=by
      field_simp [ne_of_gt (Real.sqrt_pos.mpr (quantumHighestNorm_pos q hq a b rt)),
        ne_of_gt (Real.sqrt_pos.mpr (quantumHighestNorm_pos q hq (a+h) (b+h) (typeIIBentTargetIndex h a b c d r)))]
    have hScale:typeIIShiftedBentScale q h a b c d r*U=q^(-(h:ℤ)*(k.val:ℤ))*T:=by
      rw [hU]
      unfold typeIIShiftedBentScale
      calc
        _=(q^(-(h:ℤ)*(r.val:ℤ))*q^(-(h:ℤ)*(t.val:ℤ)))*
          ((Real.sqrt (quantumHighestNorm q (a+h) (b+h) (typeIIBentTargetIndex h a b c d r))/
            Real.sqrt (quantumHighestNorm q a b rt))*
            (Real.sqrt (quantumHighestNorm q a b rt)/
            Real.sqrt (quantumHighestNorm q (a+h) (b+h) (typeIIBentTargetIndex h a b c d r))))*T:=by ring
        _=_:=by rw [hCancel,hPow,mul_one]
    change typeIIShiftedBentScale q h a b c d r*
      (((standardWeightBasis (K:=ℝ) (a+h)).tensorProduct
        ((standardWeightBasis (K:=ℝ) (b+h)).tensorProduct (standardWeightBasis (K:=ℝ) c))).repr
        (standardBentPairHighest q hq hq1 d c rs (a+h) (b+h) (typeIIBentTargetIndex h a b c d r) L hs
          (typeIIBentTarget_label h a b c d r)) (0,(standardWeightShiftIndex h b j,z)))=
      q^(-(h:ℤ)*(k.val:ℤ))*
      (((standardWeightBasis (K:=ℝ) a).tensorProduct
        ((standardWeightBasis (K:=ℝ) b).tensorProduct (standardWeightBasis (K:=ℝ) c))).repr
        (standardBentPairHighest q hq hq1 d c rs a b rt L hs ht) (0,(j,z)))
    rw [heh,he0]
    change typeIIShiftedBentScale q h a b c d r*(((-1:ℝ)^(z.val:ℤ)*S*U)/quantumWeight q L t.val)=
      q^(-(h:ℤ)*(k.val:ℤ))*(((-1:ℝ)^(z.val:ℤ)*S*T)/quantumWeight q L t.val)
    calc
      _=(((-1:ℝ)^(z.val:ℤ)*S)/quantumWeight q L t.val)*
        (typeIIShiftedBentScale q h a b c d r*U):=by ring
      _=(((-1:ℝ)^(z.val:ℤ)*S)/quantumWeight q L t.val)*(q^(-(h:ℤ)*(k.val:ℤ))*T):=by rw [hScale]
      _=_:=by ring

end AMSPhysical
#print axioms AMSPhysical.typeIIShiftedBent_coordinate_transport
