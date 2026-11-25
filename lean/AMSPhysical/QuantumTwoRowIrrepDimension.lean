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

/-- Actual pivotal trace on the independently constructed canonical two-row
irrep with Young diagram (a+b,b). No Weyl formula defines this quantity. -/
def twoRowIrrepQuantumDimension (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (a b : ℕ) : ℝ :=
  LinearMap.trace ℝ (twoRowHighestRealization q hq hq1 n hn (a+2*b) b (a+b) b (by omega) (by omega) (le_refl b)).channel
    ((twoRowHighestRealization q hq hq1 n hn (a+2*b) b (a+b) b (by omega) (by omega) (le_refl b)).channelAction
      (typeAInversePivot q n))

theorem symmetricFusionChannel_pivotal_trace (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : TwoRowFusionIndex l m) :
    LinearMap.trace ℝ (symmetricFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m r)
      (symmetricFusionChannelAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m r (typeAInversePivot q n))=
      twoRowIrrepQuantumDimension q hq hq1 n hn (l+m-2*r.val) r.val := by
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
    (normalizedTwoRowChannel_eq_actual q hq hq1 n hn l m r) (typeAInversePivot q n)
  calc
    _ = LinearMap.trace ℝ X.channel (X.channelAction (typeAInversePivot q n)) := he.symm
    _ = LinearMap.trace ℝ Y.channel (Y.channelAction (typeAInversePivot q n)) :=
      CompactHighestRealization.trace_transport (V:=V) (W:=W) (ne_of_gt hq) X Y (typeAInversePivot q n)
    _ = _ := rfl

theorem symmetricQuantumDimension_product_twoRow_fusion (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) :
    symmetricQuantumDimension q n l*symmetricQuantumDimension q n m=
      ∑ r : TwoRowFusionIndex l m,twoRowIrrepQuantumDimension q hq hq1 n hn (l+m-2*r.val) r.val := by
  let V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V:=inferInstance
  letI : Module ℝ V:=inferInstance
  change (qfactorial q (n+l)/(qfactorial q n*qfactorial q l))*
    (qfactorial q (n+m)/(qfactorial q n*qfactorial q m))=_
  rw [← typeASymmetricTensor_pivotal_dimension q hq (qInteger_denominator_ne_zero q hq hq1)]
  rw [trace_invariant_family (V:=V)
    (typeASymmetricTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    (symmetricFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m)
    (symmetricFusionChannelAt_invariant q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n hn l m)
    (symmetricFusionEquiv q hq hq1 n hn l m) rfl (typeAInversePivot q n)]
  exact Finset.sum_congr rfl (fun r _ =>symmetricFusionChannel_pivotal_trace q hq hq1 n hn l m r)

end AMSPhysical
#print axioms AMSPhysical.symmetricQuantumDimension_product_twoRow_fusion
