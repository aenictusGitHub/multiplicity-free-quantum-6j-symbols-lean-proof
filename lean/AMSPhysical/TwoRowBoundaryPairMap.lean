import TwoRowTransferRootFormula
import TwoVertexPairProjection
import QuantumOrthonormalBasis

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def twoRowPairChannelMap (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (S r l m l' m' : ℕ) (hS : l+m=S) (hS' : l'+m'=S)
    (hl : r≤l) (hm : r≤m) (hl' : r≤l') (hm' : r≤m') :
    (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) →ₗ[ℝ]
      (quantumOccupationSpace ℝ (Fin (n+1)) l' ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m') :=
  CompactHighestRealization.channelTransfer (ne_of_gt hq)
    (twoRowHighestRealization q hq hq1 n hn S r l m hS hl hm)
    (twoRowHighestRealization q hq hq1 n hn S r l' m' hS' hl' hm')

def twoRowBoundaryPairMap (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (S r l m l' m' : ℕ) (hS : l+m=S) (hS' : l'+m'=S)
    (hl : r≤l) (hm : r≤m) (hl' : r≤l') (hm' : r≤m') :
    (finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) →ₗ[ℝ]
      (finiteWeightSpace (K:=ℝ) l' ⊗[ℝ] finiteWeightSpace (K:=ℝ) m') :=
  (twoVertexTensorProjection n hn l' m').comp
    ((twoRowPairChannelMap q hq hq1 n hn S r l m l' m' hS hS' hl hm hl' hm').comp
      (twoVertexTensorEmbedding n hn l m))

/-- The complete boundary restriction of the ACTUAL physical two-row pair
map is rank independent. Every boundary coefficient is covered by the
independently proved complete standard Clebsch basis. -/
theorem twoRowBoundaryPairMap_rank_independent (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (S r l m l' m' : ℕ) (hS : l+m=S) (hS' : l'+m'=S)
    (hl : r≤l) (hm : r≤m) (hl' : r≤l') (hm' : r≤m') :
    twoRowBoundaryPairMap q hq hq1 n hn S r l m l' m' hS hS' hl hm hl' hm'=
    twoRowBoundaryPairMap q hq hq1 1 (by omega) S r l m l' m' hS hS' hl hm hl' hm' := by
  subst S
  apply (quantumOrthonormalCoupledBasis q hq hq1 l m).ext
  intro p
  rw [quantumOrthonormalCoupledBasis_apply]
  rcases p with ⟨s,k⟩
  dsimp only [twoRowBoundaryPairMap,LinearMap.comp_apply,orthonormalCoupledVector,twoRowPairChannelMap]
  by_cases hrs : r=s.val
  · subst r
    change twoVertexTensorProjection n hn l' m'
      (CompactHighestRealization.channelTransfer (ne_of_gt hq) _ _
        (twoRowRootStringAtTotal q hq hq1 n hn (l+m) s.val l m rfl hl hm
          (orthonormalWeightVector q (coupledLabel l m s) k)))=
      twoVertexTensorProjection 1 (by omega) l' m'
        (CompactHighestRealization.channelTransfer (ne_of_gt hq) _ _
          (twoRowRootStringAtTotal q hq hq1 1 (by omega) (l+m) s.val l m rfl hl hm
            (orthonormalWeightVector q (coupledLabel l m s) k)))
    rw [twoRowChannelTransfer_rootString,twoRowChannelTransfer_rootString]
    exact twoVertexTensorProjection_rootString_total_rank_independent q hq hq1 n hn
      (l+m) s.val l' m' hS' hl' hm' _
  · let r' : TwoRowFusionIndex l m:=⟨r,by omega⟩
    have hne : r'≠s:=by intro he;exact hrs (congrArg (fun x : TwoRowFusionIndex l m =>x.val) he)
    have hN:=twoRowChannelTransfer_rootString_other q hq hq1 n hn (l+m) l m l' m' rfl hS'
      r' s hne hl' hm' (orthonormalWeightVector q (coupledLabel l m s) k)
    have h1:=twoRowChannelTransfer_rootString_other q hq hq1 1 (by omega) (l+m) l m l' m' rfl hS'
      r' s hne hl' hm' (orthonormalWeightVector q (coupledLabel l m s) k)
    change twoVertexTensorProjection n hn l' m'
      (CompactHighestRealization.channelTransfer (ne_of_gt hq) _ _
        (twoRowRootStringEmbedding q hq hq1 n hn l m s (orthonormalWeightVector q (coupledLabel l m s) k)))=
      twoVertexTensorProjection 1 (by omega) l' m'
        (CompactHighestRealization.channelTransfer (ne_of_gt hq) _ _
          (twoRowRootStringEmbedding q hq hq1 1 (by omega) l m s (orthonormalWeightVector q (coupledLabel l m s) k)))
    rw [hN,h1,map_zero,map_zero]

end AMSPhysical
#print axioms AMSPhysical.twoRowBoundaryPairMap_rank_independent
