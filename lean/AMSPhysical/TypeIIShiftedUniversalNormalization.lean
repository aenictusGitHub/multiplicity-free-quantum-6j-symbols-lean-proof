import TypeIIShiftedBendingScalar
import TypeIIShiftedBoundaryTransport
import TypeIIDeterminantMetricScale
import QuantumTypeIILeftNormClosed

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical

/-- The common metric scale is obtained from actual tree norms, including
all determinant-background powers. It is independent of the channel. -/
theorem typeIIShiftedUniversalNormalization_sq (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d):
    (typeIIShiftedBentScale q h a b c d r*typeIIShiftedBendingAbs q h a b c d hbal r)^2=
      typeIIDeterminantMetricScale q h a b d*
        physicalTypeIILeftHighestNormSq q hq hq1 (h+1) (by omega) a b c d hbal r := by
  have hr:=r.isLt
  rw [mul_pow,typeIIShiftedBendingAbs_sq q hq hq1]
  unfold typeIIShiftedBentScale
  rw [mul_pow,div_pow,Real.sq_sqrt (quantumHighestNorm_pos q hq _ _ _).le,
    Real.sq_sqrt (quantumHighestNorm_pos q hq _ _ _).le,
    quantumHighestNorm_closed q hq hq1,quantumHighestNorm_closed q hq hq1,
    physicalTypeIILeftHighestNormSq_closed]
  have ha:a-r.val+r.val=a:=by omega
  have hb:b-r.val+r.val=b:=by omega
  have hL:typeIIBentLabel a b c d r=(a-r.val)+(b-r.val):=by unfold typeIIBentLabel;omega
  have he:=typeIIDeterminantMetricScale_channel q hq hq1 h (a-r.val) (b-r.val) r.val d
  rw [ha,hb] at he
  simpa only [typeIIBentTargetIndex,Fin.val_mk,Nat.add_zero,
    show a+h-(r.val+h)=a-r.val from by omega,
    show b+h-(r.val+h)=b-r.val from by omega,hL] using he

/-- Positive square roots remove every channel-dependent normalization. -/
theorem typeIIShiftedUniversalNormalization (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d):
    typeIIShiftedBentScale q h a b c d r*typeIIShiftedBendingAbs q h a b c d hbal r=
      Real.sqrt (typeIIDeterminantMetricScale q h a b d)*
        Real.sqrt (physicalTypeIILeftHighestNormSq q hq hq1 (h+1) (by omega) a b c d hbal r) := by
  have he:=typeIIShiftedUniversalNormalization_sq q hq hq1 h a b c d hbal r
  have hp:=mul_pos (typeIIShiftedBentScale_pos q hq h a b c d r)
    (typeIIShiftedBendingAbs_pos q hq h a b c d hbal r)
  have hC:=(typeIIDeterminantMetricScale_pos q hq h a b d).le
  have hN:=physicalTypeIILeftHighest_norm_pos q hq hq1 (h+1) (by omega) a b c d hbal r
  change 0<physicalTypeIILeftHighestNormSq q hq hq1 (h+1) (by omega) a b c d hbal r at hN
  have hs:(Real.sqrt (typeIIDeterminantMetricScale q h a b d)*
      Real.sqrt (physicalTypeIILeftHighestNormSq q hq hq1 (h+1) (by omega) a b c d hbal r))^2=
      typeIIDeterminantMetricScale q h a b d*
        physicalTypeIILeftHighestNormSq q hq hq1 (h+1) (by omega) a b c d hbal r:=by
    rw [mul_pow,Real.sq_sqrt hC,Real.sq_sqrt hN.le]
  have hpos:=mul_nonneg (Real.sqrt_nonneg (typeIIDeterminantMetricScale q h a b d))
    (Real.sqrt_nonneg (physicalTypeIILeftHighestNormSq q hq hq1 (h+1) (by omega) a b c d hbal r))
  nlinarith

end AMSPhysical
#print axioms AMSPhysical.typeIIShiftedUniversalNormalization
