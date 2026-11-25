import QuantumMixedPivotal
import QuantumMixedFusionRealization
import CompactHighestTrace
import TraceRestrictionCongruence
import TraceInvariantFusion

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 180000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def symmetricQuantumDimension (q : ℝ) (n L : ℕ) : ℝ :=
  qfactorial q (n+L)/(qfactorial q n*qfactorial q L)

/-- Defined from the ACTUAL restricted presented-algebra pivotal operator
on the independently constructed canonical highest-weight irrep. -/
def mixedIrrepQuantumDimension (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (a b : ℕ) : ℝ :=
  LinearMap.trace ℝ (mixedHighestRealization q hq hq1 n hn 0 a b).channel
    ((mixedHighestRealization q hq hq1 n hn 0 a b).channelAction (typeAInversePivot q n))

theorem mixedFusionChannel_pivotal_trace (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : MixedFusionIndex l m) :
    LinearMap.trace ℝ (mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m r)
      (mixedFusionChannelAction q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m r (typeAInversePivot q n))=
      mixedIrrepQuantumDimension q hq hq1 n hn (l-r.val) (m-r.val) := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  let W := quantumOccupationSpace ℝ (Fin (n+1)) (0+(l-r.val)) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (0+(m-r.val))
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  let X:=mixedFusionHighestRealization q hq hq1 n hn l m r
  let Y:=mixedHighestRealization q hq hq1 n hn 0 (l-r.val) (m-r.val)
  have he:=trace_invariantRestriction_congr (V:=V)
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    X.channel (mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m r)
    (algebraCyclicSpan_invariant X.action X.highest)
    (mixedFusionChannelAt_invariant q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m r)
    (mixedFusionHighestRealization_channel q hq hq1 n hn l m r) (typeAInversePivot q n)
  calc
    _ = LinearMap.trace ℝ X.channel (X.channelAction (typeAInversePivot q n)) := he.symm
    _ = LinearMap.trace ℝ Y.channel (Y.channelAction (typeAInversePivot q n)) :=
      CompactHighestRealization.trace_transport (V:=V) (W:=W) (ne_of_gt hq) X Y (typeAInversePivot q n)
    _ = _ := rfl

/-- A physical quantum-character identity derived from actual trace
additivity, complete fusion and the proved canonical full-algebra transports. -/
theorem symmetricQuantumDimension_product_fusion (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) :
    symmetricQuantumDimension q n l*symmetricQuantumDimension q n m=
      ∑ r : MixedFusionIndex l m,mixedIrrepQuantumDimension q hq hq1 n hn (l-r.val) (m-r.val) := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  change (qfactorial q (n+l)/(qfactorial q n*qfactorial q l))*
    (qfactorial q (n+m)/(qfactorial q n*qfactorial q m))=_
  rw [← typeAMixedTensor_pivotal_dimension q hq (qInteger_denominator_ne_zero q hq hq1)]
  rw [trace_invariant_family (V:=V)
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    (mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    (mixedFusionChannelAt_invariant q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m)
    (mixedFusionEquiv q hq hq1 n hn l m) rfl (typeAInversePivot q n)]
  apply Finset.sum_congr rfl
  intro r hr
  exact mixedFusionChannel_pivotal_trace q hq hq1 n hn l m r

end AMSPhysical
#print axioms AMSPhysical.symmetricQuantumDimension_product_fusion
