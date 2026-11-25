import GlobalMixedPairRealizations
import QuantumPhysicalTripleInstances

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

instance quantumPhysicalPairFinite (n l m : ℕ) : Module.Finite ℝ
    (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :=
  Module.Finite.of_basis ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m))

theorem globalMixedPairRealization_channel (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (p s r : ℕ) :
    (globalMixedPairRealization q hq hq1 n hn p s r).channel =
      mixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n
        (p+r) (s+r) (globalMixedPairIndex p s r) :=
  mixedFusionHighestRealization_channel q hq hq1 n hn (p+r) (s+r) (globalMixedPairIndex p s r)

def globalMixedPairTransfer (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (p s r t : ℕ) :=
  (globalMixedPairRealization q hq hq1 n hn p s r).channelTransfer (ne_of_gt hq)
    (globalMixedPairRealization q hq hq1 n hn p s t)

theorem globalMixedPairTransfer_comp (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (p s r t u : ℕ) :
    (globalMixedPairTransfer q hq hq1 n hn p s t u).comp
      (globalMixedPairTransfer q hq hq1 n hn p s r t) =
      globalMixedPairTransfer q hq hq1 n hn p s r u :=
  CompactHighestRealization.channelTransfer_comp (ne_of_gt hq)
    (globalMixedPairRealization q hq hq1 n hn p s r)
    (globalMixedPairRealization q hq hq1 n hn p s t)
    (globalMixedPairRealization q hq hq1 n hn p s u)

theorem globalMixedPairTransfer_self_on_channel (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (p s r : ℕ)
    (x : (globalMixedPairRealization q hq hq1 n hn p s r).channel) :
    globalMixedPairTransfer q hq hq1 n hn p s r r x.val=x.val := by
  change ((globalMixedPairRealization q hq hq1 n hn p s r).transport (ne_of_gt hq)
    (globalMixedPairRealization q hq hq1 n hn p s r)
      ((globalMixedPairRealization q hq hq1 n hn p s r).channelProjection x.val)).val=x.val
  rw [CompactHighestRealization.channelProjection_subtype,CompactHighestRealization.transport_self]

theorem globalMixedPair_creation_transfer (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (p s r : ℕ)
    (x : (globalMixedPairRealization q hq hq1 n hn p s r).channel) :
    mixedFiniteCreation q n (p+r) (s+r) x.val =
      mixedCreationUnitScale q n (p+r) (s+r) (globalMixedPairIndex p s r) •
        globalMixedPairTransfer q hq hq1 n hn p s r (r+1) x.val := by
  rw [globalMixedPair_creation_transport]
  change _ = _ • (((globalMixedPairRealization q hq hq1 n hn p s r).transport (ne_of_gt hq)
    (globalMixedPairRealization q hq hq1 n hn p s (r+1)))
      ((globalMixedPairRealization q hq hq1 n hn p s r).channelProjection x.val)).val
  rw [CompactHighestRealization.channelProjection_subtype]

end AMSPhysical
#print axioms AMSPhysical.globalMixedPairTransfer_comp
#print axioms AMSPhysical.globalMixedPair_creation_transfer
