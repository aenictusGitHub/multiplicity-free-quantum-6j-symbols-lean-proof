import GlobalMixedOrientationBoundary
import GlobalMixedPairTransfers
import QuantumReverseMixedCreation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem normalizedReverseMixedFusionHighest_reflection (q : ℝ) (n l m : ℕ) (r : MixedFusionIndex l m) :
    normalizedReverseMixedFusionHighestAt q n l m r =
      mixedReflection n l m (normalizedMixedFusionHighestAt q n l m r) := by
  unfold normalizedReverseMixedFusionHighestAt normalizedMixedFusionHighestAt reverseMixedFusionHighestAt
  rw [map_smul]

theorem globalReverseMixedPairRealization_channel (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (p s r : ℕ) :
    (globalReverseMixedPairRealization q hq hq1 n hn p s r).channel =
      reverseMixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n
        (s+r) (p+r) (globalMixedPairIndex s p r) :=
  reverseMixedFusionHighestRealization_channel q hq hq1 n hn (s+r) (p+r) (globalMixedPairIndex s p r)

theorem globalReverseMixedPair_creation_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (p s r : ℕ) :
    reverseMixedFiniteCreation q n (s+r) (p+r)
      (globalReverseMixedPairRealization q hq hq1 n hn p s r).highest =
      mixedCreationUnitScale q n (s+r) (p+r) (globalMixedPairIndex s p r) •
        (globalReverseMixedPairRealization q hq hq1 n hn p s (r+1)).highest := by
  change reverseMixedFiniteCreation q n (s+r) (p+r)
    (normalizedReverseMixedFusionHighestAt q n (s+r) (p+r) (globalMixedPairIndex s p r)) =
      _ • normalizedReverseMixedFusionHighestAt q n (s+(r+1)) (p+(r+1)) (globalMixedPairIndex s p (r+1))
  rw [normalizedReverseMixedFusionHighest_reflection,normalizedReverseMixedFusionHighest_reflection]
  unfold reverseMixedFiniteCreation
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
  rw [mixedFiniteCreation_normalized_highest q hq hq1 n hn,map_smul]
  rfl

theorem globalReverseMixedPair_creation_transport (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (p s r : ℕ)
    (x : (globalReverseMixedPairRealization q hq hq1 n hn p s r).channel) :
    reverseMixedFiniteCreation q n (s+r) (p+r) x.val =
      mixedCreationUnitScale q n (s+r) (p+r) (globalMixedPairIndex s p r) •
        ((globalReverseMixedPairRealization q hq hq1 n hn p s r).transport (ne_of_gt hq)
          (globalReverseMixedPairRealization q hq hq1 n hn p s (r+1)) x).val := by
  exact CompactHighestRealization.intertwiner_scalar_highest (ne_of_gt hq)
    (globalReverseMixedPairRealization q hq hq1 n hn p s r)
    (globalReverseMixedPairRealization q hq hq1 n hn p s (r+1))
    (reverseMixedFiniteCreation q n (s+r) (p+r)) _
    (reverseMixedFiniteCreation_intertwines q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (s+r) (p+r))
    (globalReverseMixedPair_creation_highest q hq hq1 n hn p s r) x

def globalReverseMixedPairTransfer (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (p s r t : ℕ) :=
  (globalReverseMixedPairRealization q hq hq1 n hn p s r).channelTransfer (ne_of_gt hq)
    (globalReverseMixedPairRealization q hq hq1 n hn p s t)

theorem globalReverseMixedPairTransfer_comp (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (p s r t u : ℕ) :
    (globalReverseMixedPairTransfer q hq hq1 n hn p s t u).comp
      (globalReverseMixedPairTransfer q hq hq1 n hn p s r t) =
      globalReverseMixedPairTransfer q hq hq1 n hn p s r u :=
  CompactHighestRealization.channelTransfer_comp (ne_of_gt hq)
    (globalReverseMixedPairRealization q hq hq1 n hn p s r)
    (globalReverseMixedPairRealization q hq hq1 n hn p s t)
    (globalReverseMixedPairRealization q hq hq1 n hn p s u)

theorem globalReverseMixedPair_creation_transfer (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (p s r : ℕ)
    (x : (globalReverseMixedPairRealization q hq hq1 n hn p s r).channel) :
    reverseMixedFiniteCreation q n (s+r) (p+r) x.val =
      mixedCreationUnitScale q n (s+r) (p+r) (globalMixedPairIndex s p r) •
        globalReverseMixedPairTransfer q hq hq1 n hn p s r (r+1) x.val := by
  rw [globalReverseMixedPair_creation_transport]
  change _ = _ • (((globalReverseMixedPairRealization q hq hq1 n hn p s r).transport (ne_of_gt hq)
    (globalReverseMixedPairRealization q hq hq1 n hn p s (r+1)))
      ((globalReverseMixedPairRealization q hq hq1 n hn p s r).channelProjection x.val)).val
  rw [CompactHighestRealization.channelProjection_subtype]

theorem globalReverseMixedPairTransfer_self_on_channel (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (p s r : ℕ)
    (x : (globalReverseMixedPairRealization q hq hq1 n hn p s r).channel) :
    globalReverseMixedPairTransfer q hq hq1 n hn p s r r x.val=x.val := by
  change ((globalReverseMixedPairRealization q hq hq1 n hn p s r).transport (ne_of_gt hq)
    (globalReverseMixedPairRealization q hq hq1 n hn p s r)
      ((globalReverseMixedPairRealization q hq hq1 n hn p s r).channelProjection x.val)).val=x.val
  rw [CompactHighestRealization.channelProjection_subtype,CompactHighestRealization.transport_self]

end AMSPhysical
#print axioms AMSPhysical.globalReverseMixedPair_creation_transfer
