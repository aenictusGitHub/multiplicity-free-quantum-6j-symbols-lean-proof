import TwoRowTransportRootStrings
import CompactHighestProjectionOrthogonal
import QuantumTwoRowChannelEquality

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- The ACTUAL full two-row pair channel map acts on its first-root string
by the standard rank-two string with exactly the same normalization. -/
theorem twoRowChannelTransfer_rootString (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (S r l m l' m' : ℕ) (hS : l+m=S) (hS' : l'+m'=S)
    (hl : r≤l) (hm : r≤m) (hl' : r≤l') (hm' : r≤m')
    (v : finiteWeightSpace (K:=ℝ) (S-2*r)) :
    CompactHighestRealization.channelTransfer (ne_of_gt hq)
      (twoRowHighestRealization q hq hq1 n hn S r l m hS hl hm)
      (twoRowHighestRealization q hq hq1 n hn S r l' m' hS' hl' hm')
      (twoRowRootStringAtTotal q hq hq1 n hn S r l m hS hl hm v)=
    twoRowRootStringAtTotal q hq hq1 n hn S r l' m' hS' hl' hm' v := by
  let X:=twoRowHighestRealization q hq hq1 n hn S r l m hS hl hm
  let Y:=twoRowHighestRealization q hq hq1 n hn S r l' m' hS' hl' hm'
  have hp:=X.channelProjection_subtype
    ⟨twoRowRootStringAtTotal q hq hq1 n hn S r l m hS hl hm v,
      twoRowRootStringAtTotal_mem q hq hq1 n hn S r l m hS hl hm v⟩
  change (X.transport (ne_of_gt hq) Y
    (X.channelProjection (twoRowRootStringAtTotal q hq hq1 n hn S r l m hS hl hm v))).val=_
  rw [hp]
  exact twoRowCanonicalTransport_rootString q hq hq1 n hn S r l m l' m' hS hS' hl hm hl' hm' v

/-- Every other standard first-root channel is killed by the actual higher
pair projection. Together these equations determine the entire boundary
restriction of the physical pair map. -/
theorem twoRowChannelTransfer_rootString_other (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (S l m l' m' : ℕ) (hS : l+m=S) (hS' : l'+m'=S)
    (r s : TwoRowFusionIndex l m) (hrs : r≠s) (hl' : r.val≤l') (hm' : r.val≤m')
    (v : finiteWeightSpace (K:=ℝ) (coupledLabel l m s)) :
    CompactHighestRealization.channelTransfer (ne_of_gt hq)
      (twoRowHighestRealization q hq hq1 n hn S r.val l m hS (channel_left_bound l m r) (channel_right_bound l m r))
      (twoRowHighestRealization q hq hq1 n hn S r.val l' m' hS' hl' hm')
      (twoRowRootStringEmbedding q hq hq1 n hn l m s v)=0 := by
  apply CompactHighestRealization.channelTransfer_zero_of_orthogonal
  intro w hw
  exact normalizedTwoRowChannels_orthogonal q hq hq1 n hn l m r s hrs w hw _
    (twoRowRootStringEmbedding_mem_channel q hq hq1 n hn l m s v)

end AMSPhysical
#print axioms AMSPhysical.twoRowChannelTransfer_rootString
#print axioms AMSPhysical.twoRowChannelTransfer_rootString_other
