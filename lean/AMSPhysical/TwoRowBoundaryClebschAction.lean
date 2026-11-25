import StandardClebschAtTotal
import TwoRowBoundaryPairMap

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem twoRowBoundaryPairMap_selected (q:ℝ) (hq:0<q) (hq1:q≠1) (n:ℕ) (hn:0<n)
    (S r l m l' m':ℕ) (hS:l+m=S) (hS':l'+m'=S)
    (hl:r≤l) (hm:r≤m) (hl':r≤l') (hm':r≤m') (v:finiteWeightSpace (K:=ℝ) (S-2*r)) :
    twoRowBoundaryPairMap q hq hq1 n hn S r l m l' m' hS hS' hl hm hl' hm'
      (standardClebschAtTotal q hq hq1 S r l m hS hl hm v)=
      standardClebschAtTotal q hq hq1 S r l' m' hS' hl' hm' v := by
  simp only [twoRowBoundaryPairMap,LinearMap.comp_apply]
  rw [standardClebschAtTotal_embedding]
  change twoVertexTensorProjection n hn l' m'
    (CompactHighestRealization.channelTransfer (ne_of_gt hq) _ _
      (twoRowRootStringAtTotal q hq hq1 n hn S r l m hS hl hm v))=_
  rw [twoRowChannelTransfer_rootString,twoRowRootStringAtTotal_projection]

theorem twoRowBoundaryPairMap_other (q:ℝ) (hq:0<q) (hq1:q≠1) (n:ℕ) (hn:0<n)
    (S l m l' m':ℕ) (hS:l+m=S) (hS':l'+m'=S)
    (r s:TwoRowFusionIndex l m) (hrs:r≠s) (hl':r.val≤l') (hm':r.val≤m')
    (v:finiteWeightSpace (K:=ℝ) (coupledLabel l m s)) :
    twoRowBoundaryPairMap q hq hq1 n hn S r.val l m l' m' hS hS'
      (channel_left_bound l m r) (channel_right_bound l m r) hl' hm'
      (unitaryQuantumClebschMap q hq hq1 l m s v)=0 := by
  simp only [twoRowBoundaryPairMap,LinearMap.comp_apply]
  change twoVertexTensorProjection n hn l' m'
    (CompactHighestRealization.channelTransfer (ne_of_gt hq) _ _
      (twoRowRootStringEmbedding q hq hq1 n hn l m s v))=0
  rw [twoRowChannelTransfer_rootString_other q hq hq1 n hn S l m l' m' hS hS' r s hrs hl' hm',map_zero]

end AMSPhysical
#print axioms AMSPhysical.twoRowBoundaryPairMap_selected
#print axioms AMSPhysical.twoRowBoundaryPairMap_other
