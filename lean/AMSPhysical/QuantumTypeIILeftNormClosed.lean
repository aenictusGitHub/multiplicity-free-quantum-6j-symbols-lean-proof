import QuantumTypeIILeftNormTrace
import QuantumTwoRowPositiveDimension
import QuantumTwoRowDimensionClosed

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem typeIILeftSource_positivePivot_trace (q:ℝ) (hq:0<q) (hq1:q≠1)
    (n:ℕ) (hn:0<n) (a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d) :
    LinearMap.trace ℝ (typeIILeftSource q hq hq1 n hn a b c d hbal r).channel
      ((typeIILeftSource q hq hq1 n hn a b c d hbal r).channelAction (typeAPositivePivot q (ne_of_gt hq) n))=
      twoRowIrrepQuantumDimension q hq hq1 n hn ((a-r.val)+(b-r.val)) r.val := by
  let V:=quantumOccupationSpace ℝ (Fin (n+1)) d ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  let X:=typeIILeftSource q hq hq1 n hn a b c d hbal r
  let r':TwoRowFusionIndex d c:=⟨r.val,by have hr:=r.isLt;omega⟩
  have heq:X.channel=symmetricFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn d c r' :=
    normalizedTwoRowChannel_eq_actual q hq hq1 n hn d c r'
  have he:=trace_invariantRestriction_congr (V:=V)
    (typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n d c)
    X.channel (symmetricFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn d c r')
    (algebraCyclicSpan_invariant X.action X.highest)
    (symmetricFusionChannelAt_invariant q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn d c r')
    heq (typeAPositivePivot q (ne_of_gt hq) n)
  change LinearMap.trace ℝ X.channel (X.channelAction (typeAPositivePivot q (ne_of_gt hq) n))=_ at he
  rw [he]
  change LinearMap.trace ℝ (symmetricFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn d c r')
    (symmetricFusionChannelAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn d c r'
      (typeAPositivePivot q (ne_of_gt hq) n))=_
  rw [symmetricFusionChannel_positivePivot_trace_closed q hq hq1 n hn d c r']
  congr 1
  have hr:=r.isLt
  change d+c-2*r.val=(a-r.val)+(b-r.val)
  omega

/-- Closed actual physical Type-II tree normalization, proved from the
literal physical cup, positive metric, actual partial-channel isometry,
actual pivotal trace and complete fusion. No AMS overlap is assumed. -/
theorem physicalTypeIILeftHighestNormSq_closed (q:ℝ) (hq:0<q) (hq1:q≠1)
    (n:ℕ) (hn:0<n) (a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d) :
    physicalTypeIILeftHighestNormSq q hq hq1 n hn a b c d hbal r=
      twoRowIrrepQuantumDimension q hq hq1 n hn ((a-r.val)+(b-r.val)) r.val/symmetricQuantumDimension q n d := by
  have hd:0<symmetricQuantumDimension q n d:=
    div_pos (qfactorial_pos q hq _) (mul_pos (qfactorial_pos q hq _) (qfactorial_pos q hq _))
  apply (eq_div_iff (ne_of_gt hd)).mpr
  rw [physicalTypeIILeftHighestNormSq_trace,typeIILeftSource_positivePivot_trace]

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIILeftHighestNormSq_closed
