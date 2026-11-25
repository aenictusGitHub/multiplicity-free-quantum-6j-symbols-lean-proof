import TwoRowBoundaryPairMap

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem twoVertexTensorEmbedding_rootString_total_projection (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (S r l m : ℕ) (hS : l+m=S) (hl : r≤l) (hm : r≤m)
    (v : finiteWeightSpace (K:=ℝ) (S-2*r)) :
    twoVertexTensorEmbedding n hn l m
      (twoVertexTensorProjection n hn l m (twoRowRootStringAtTotal q hq hq1 n hn S r l m hS hl hm v))=
      twoRowRootStringAtTotal q hq hq1 n hn S r l m hS hl hm v := by
  subst S
  change twoVertexTensorEmbedding n hn l m
    (twoVertexTensorProjection n hn l m
      (twoVertexTensorEmbedding n hn l m (unitaryQuantumClebschMap q hq hq1 l m ⟨r,by omega⟩ v)))=_
  rw [twoVertexTensorProjection_embedding]
  rfl

/-- The whole ACTUAL pair map preserves the two-coordinate boundary, not
only its compressed coefficients. This is a literal commuting square. -/
theorem twoRowPairChannelMap_boundary_lift (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (S r l m l' m' : ℕ) (hS : l+m=S) (hS' : l'+m'=S)
    (hl : r≤l) (hm : r≤m) (hl' : r≤l') (hm' : r≤m') :
    (twoRowPairChannelMap q hq hq1 n hn S r l m l' m' hS hS' hl hm hl' hm').comp
      (twoVertexTensorEmbedding n hn l m)=
    (twoVertexTensorEmbedding n hn l' m').comp
      (twoRowBoundaryPairMap q hq hq1 1 (by omega) S r l m l' m' hS hS' hl hm hl' hm') := by
  rw [← twoRowBoundaryPairMap_rank_independent q hq hq1 n hn S r l m l' m' hS hS' hl hm hl' hm']
  subst S
  apply (quantumOrthonormalCoupledBasis q hq hq1 l m).ext
  intro p
  rw [quantumOrthonormalCoupledBasis_apply]
  rcases p with ⟨s,k⟩
  dsimp only [twoRowBoundaryPairMap,LinearMap.comp_apply,orthonormalCoupledVector,twoRowPairChannelMap]
  by_cases hrs : r=s.val
  · subst r
    change CompactHighestRealization.channelTransfer (ne_of_gt hq) _ _
      (twoRowRootStringAtTotal q hq hq1 n hn (l+m) s.val l m rfl hl hm (orthonormalWeightVector q (coupledLabel l m s) k))=
      twoVertexTensorEmbedding n hn l' m'
        (twoVertexTensorProjection n hn l' m'
          (CompactHighestRealization.channelTransfer (ne_of_gt hq) _ _
            (twoRowRootStringAtTotal q hq hq1 n hn (l+m) s.val l m rfl hl hm (orthonormalWeightVector q (coupledLabel l m s) k))))
    rw [twoRowChannelTransfer_rootString]
    exact (twoVertexTensorEmbedding_rootString_total_projection q hq hq1 n hn (l+m) s.val l' m' hS' hl' hm' _).symm
  · let r' : TwoRowFusionIndex l m:=⟨r,by omega⟩
    have hne : r'≠s:=by intro he;exact hrs (congrArg (fun x : TwoRowFusionIndex l m =>x.val) he)
    have hN:=twoRowChannelTransfer_rootString_other q hq hq1 n hn (l+m) l m l' m' rfl hS'
      r' s hne hl' hm' (orthonormalWeightVector q (coupledLabel l m s) k)
    change CompactHighestRealization.channelTransfer (ne_of_gt hq) _ _
      (twoRowRootStringEmbedding q hq hq1 n hn l m s (orthonormalWeightVector q (coupledLabel l m s) k))=
      twoVertexTensorEmbedding n hn l' m'
        (twoVertexTensorProjection n hn l' m'
          (CompactHighestRealization.channelTransfer (ne_of_gt hq) _ _
            (twoRowRootStringEmbedding q hq hq1 n hn l m s (orthonormalWeightVector q (coupledLabel l m s) k))))
    rw [hN,map_zero,map_zero]

end AMSPhysical
#print axioms AMSPhysical.twoRowPairChannelMap_boundary_lift
