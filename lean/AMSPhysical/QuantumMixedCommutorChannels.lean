import QuantumMixedCommutor
import OrthogonalFusionChannels

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- The constructed actual mixed commutor maps EACH independently defined
irreducible physical channel onto its counterpart in reverse tensor order. -/
theorem physicalMixedCommutor_channel_map (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : MixedFusionIndex l m) :
    (mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m r).map
      (physicalMixedCommutor q hq hq1 n hn l m).toLinearMap=
    reverseMixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n m l (mixedFusionSwapIndex r) := by
  let V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  let W:=quantumOccupationSpace ℝ (Fin (n+1)) m ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) l
  letI : AddCommGroup V:=inferInstance
  letI : Module ℝ V:=inferInstance
  letI : AddCommGroup W:=inferInstance
  letI : Module ℝ W:=inferInstance
  rw [← mixedFusionHighestRealization_channel q hq hq1 n hn l m r,
    ← reverseMixedFusionHighestRealization_channel q hq hq1 n hn m l (mixedFusionSwapIndex r)]
  exact orthogonalFusionTransport_channel_map (V:=V) (W:=W)
    (mixedTensorBilin q n l m) (reverseMixedTensorBilin q n m l)
    (mixedTensorBilin_definite q hq n l m) (reverseMixedTensorBilin_definite q hq n m l)
    (fun r =>(mixedCommutorSourceRealization q hq hq1 n hn l m r).channel)
    (fun r =>(mixedCommutorTargetRealization q hq hq1 n hn l m r).channel)
    (mixedCommutorSource_orthogonal q hq hq1 n hn l m)
    (mixedCommutorTarget_orthogonal q hq hq1 n hn l m)
    (mixedCommutorSource_span q hq hq1 n hn l m)
    (mixedCommutorTarget_span q hq hq1 n hn l m)
    (fun r =>CompactHighestRealization.transport (ne_of_gt hq)
      (mixedCommutorSourceRealization q hq hq1 n hn l m r)
      (mixedCommutorTargetRealization q hq hq1 n hn l m r))
    r

end AMSPhysical
#print axioms AMSPhysical.physicalMixedCommutor_channel_map
