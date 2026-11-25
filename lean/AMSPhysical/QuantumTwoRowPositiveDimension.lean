import QuantumPositivePivot
import QuantumTwoRowDimensionDifference
import QuantumSymmetricPivotal
import QuantumTwoRowChannelEquality
import CompactHighestTrace
import TraceRestrictionCongruence
import TraceInvariantFusion
import QuantumMixedIrrepDimension

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- Actual positive-pivot trace on the independently constructed canonical two-row
irrep with Young diagram (a+b,b). No Weyl formula defines this quantity. -/
def twoRowIrrepPositiveDimension (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (a b : ℕ) : ℝ :=
  LinearMap.trace ℝ (twoRowHighestRealization q hq hq1 n hn (a+2*b) b (a+b) b (by omega) (by omega) (le_refl b)).channel
    ((twoRowHighestRealization q hq hq1 n hn (a+2*b) b (a+b) b (by omega) (by omega) (le_refl b)).channelAction
      (typeAPositivePivot q (ne_of_gt hq) n))

theorem symmetricFusionChannel_positivePivot_trace (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : TwoRowFusionIndex l m) :
    LinearMap.trace ℝ (symmetricFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m r)
      (symmetricFusionChannelAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m r (typeAPositivePivot q (ne_of_gt hq) n))=
      twoRowIrrepPositiveDimension q hq hq1 n hn (l+m-2*r.val) r.val := by
  let a:=l+m-2*r.val
  have hr:=r.isLt
  have hS : l+m=a+2*r.val := by dsimp only [a];omega
  let V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  let W:=quantumOccupationSpace ℝ (Fin (n+1)) (a+r.val) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) r.val
  letI : AddCommGroup V:=inferInstance
  letI : Module ℝ V:=inferInstance
  letI : AddCommGroup W:=inferInstance
  letI : Module ℝ W:=inferInstance
  let X:=twoRowHighestRealization q hq hq1 n hn (a+2*r.val) r.val l m hS
    (channel_left_bound l m r) (channel_right_bound l m r)
  let Y:=twoRowHighestRealization q hq hq1 n hn (a+2*r.val) r.val (a+r.val) r.val (by omega) (by omega) (le_refl r.val)
  have he:=trace_invariantRestriction_congr (V:=V)
    (typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    X.channel (symmetricFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m r)
    (algebraCyclicSpan_invariant X.action X.highest)
    (symmetricFusionChannelAt_invariant q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m r)
    (normalizedTwoRowChannel_eq_actual q hq hq1 n hn l m r) (typeAPositivePivot q (ne_of_gt hq) n)
  calc
    _ = LinearMap.trace ℝ X.channel (X.channelAction (typeAPositivePivot q (ne_of_gt hq) n)) := he.symm
    _ = LinearMap.trace ℝ Y.channel (Y.channelAction (typeAPositivePivot q (ne_of_gt hq) n)) :=
      CompactHighestRealization.trace_transport (V:=V) (W:=W) (ne_of_gt hq) X Y (typeAPositivePivot q (ne_of_gt hq) n)
    _ = _ := rfl

theorem symmetricQuantumDimension_product_twoRow_positiveFusion (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) :
    symmetricQuantumDimension q n l*symmetricQuantumDimension q n m=
      ∑ r : TwoRowFusionIndex l m,twoRowIrrepPositiveDimension q hq hq1 n hn (l+m-2*r.val) r.val := by
  let V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V:=inferInstance
  letI : Module ℝ V:=inferInstance
  change (qfactorial q (n+l)/(qfactorial q n*qfactorial q l))*
    (qfactorial q (n+m)/(qfactorial q n*qfactorial q m))=_
  rw [← typeASymmetricTensor_positivePivot_dimension q hq (qInteger_denominator_ne_zero q hq hq1)]
  rw [trace_invariant_family (V:=V)
    (typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    (symmetricFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m)
    (symmetricFusionChannelAt_invariant q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m)
    (symmetricFusionEquiv q hq hq1 n hn l m) rfl (typeAPositivePivot q (ne_of_gt hq) n)]
  exact Finset.sum_congr rfl (fun r _ =>symmetricFusionChannel_positivePivot_trace q hq hq1 n hn l m r)

theorem twoRowIrrepPositiveDimension_eq (q:ℝ) (hq:0<q) (hq1:q≠1)
    (n:ℕ) (hn:0<n) (a b:ℕ) :
    twoRowIrrepPositiveDimension q hq hq1 n hn a b=twoRowIrrepQuantumDimension q hq hq1 n hn a b := by
  cases b with
  | zero =>
    rw [twoRowFusionSum_right_zero (symmetricQuantumDimension q n) (twoRowIrrepPositiveDimension q hq hq1 n hn)
      (symmetricQuantumDimension_product_twoRow_positiveFusion q hq hq1 n hn),
      symmetricQuantumDimension_zero q hq,mul_one,twoRowIrrepQuantumDimension_right_zero q hq hq1]
  | succ b =>
    rw [twoRowFusionSum_invert_succ (symmetricQuantumDimension q n) (twoRowIrrepPositiveDimension q hq hq1 n hn)
      (symmetricQuantumDimension_product_twoRow_positiveFusion q hq hq1 n hn),twoRowIrrepQuantumDimension_succ q hq hq1]

theorem symmetricFusionChannel_positivePivot_trace_closed (q:ℝ) (hq:0<q) (hq1:q≠1)
    (n:ℕ) (hn:0<n) (l m:ℕ) (r:TwoRowFusionIndex l m) :
    LinearMap.trace ℝ (symmetricFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m r)
      (symmetricFusionChannelAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m r
        (typeAPositivePivot q (ne_of_gt hq) n))=
      twoRowIrrepQuantumDimension q hq hq1 n hn (l+m-2*r.val) r.val := by
  rw [symmetricFusionChannel_positivePivot_trace,twoRowIrrepPositiveDimension_eq]

end AMSPhysical
#print axioms AMSPhysical.symmetricQuantumDimension_product_twoRow_positiveFusion

#print axioms AMSPhysical.symmetricFusionChannel_positivePivot_trace_closed
