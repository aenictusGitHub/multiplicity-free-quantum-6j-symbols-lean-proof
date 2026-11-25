import TwoRowBackBoundaryLift
import TwoVertexPairProjectionAdjoint
import AdjointBoundaryProjection

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3600000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem twoVertexStandardPairBilin_symm (q : ℝ) (l m : ℕ)
    (v w : finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) :
    quantumTensorBilin q l m v w=quantumTensorBilin q l m w v :=
  finiteWeightedPair_symm _ _ v w

theorem twoRowBoundaryPairMap_adjoint (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (S r l m l' m' : ℕ) (hS : l+m=S) (hS' : l'+m'=S)
    (hl : r≤l) (hm : r≤m) (hl' : r≤l') (hm' : r≤m')
    (u : finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m)
    (y : finiteWeightSpace (K:=ℝ) l' ⊗[ℝ] finiteWeightSpace (K:=ℝ) m') :
    quantumTensorBilin q l' m'
      (twoRowBoundaryPairMap q hq hq1 n hn S r l m l' m' hS hS' hl hm hl' hm' u) y=
      quantumTensorBilin q l m u
        (twoRowBoundaryBackMap q hq hq1 n hn S r l m l' m' hS hS' hl hm hl' hm' y) := by
  let V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  let W:=quantumOccupationSpace ℝ (Fin (n+1)) l' ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m'
  let V2:=finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m
  let W2:=finiteWeightSpace (K:=ℝ) l' ⊗[ℝ] finiteWeightSpace (K:=ℝ) m'
  letI : AddCommGroup V:=inferInstance
  letI : Module ℝ V:=inferInstance
  letI : AddCommGroup W:=inferInstance
  letI : Module ℝ W:=inferInstance
  letI : AddCommGroup V2:=inferInstance
  letI : Module ℝ V2:=inferInstance
  letI : AddCommGroup W2:=inferInstance
  letI : Module ℝ W2:=inferInstance
  exact compressed_adjoint_pair (V:=V) (W:=W) (V₂:=V2) (W₂:=W2)
    (symmetricTensorBilin q n l m) (symmetricTensorBilin q n l' m')
    (quantumTensorBilin q l m) (quantumTensorBilin q l' m')
    (symmetricTensorBilin_symm q n l' m') (twoVertexStandardPairBilin_symm q l' m')
    (twoVertexTensorEmbedding n hn l m) (twoVertexTensorProjection n hn l m)
    (twoVertexTensorEmbedding n hn l' m') (twoVertexTensorProjection n hn l' m')
    (twoVertexTensorProjection_adjoint q hq hq1 n hn l m)
    (twoVertexTensorProjection_adjoint q hq hq1 n hn l' m')
    (twoRowPairChannelMap q hq hq1 n hn S r l m l' m' hS hS' hl hm hl' hm')
    (twoRowPairBackMap q hq hq1 n hn S r l m l' m' hS hS' hl hm hl' hm')
    (CompactHighestRealization.channelTransfer_adjoint (V:=V) (W:=W) (ne_of_gt hq)
      (twoRowHighestRealization q hq hq1 n hn S r l m hS hl hm)
      (twoRowHighestRealization q hq hq1 n hn S r l' m' hS' hl' hm')) u y

/-- FULL projection naturality for arbitrary actual input vectors. Thus
higher occupation components cannot contribute spuriously to a two-vertex
output coefficient of the physical pair map. -/
theorem twoRowPairChannelMap_boundary_projection (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (S r l m l' m' : ℕ) (hS : l+m=S) (hS' : l'+m'=S)
    (hl : r≤l) (hm : r≤m) (hl' : r≤l') (hm' : r≤m')
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :
    twoVertexTensorProjection n hn l' m'
      (twoRowPairChannelMap q hq hq1 n hn S r l m l' m' hS hS' hl hm hl' hm' v)=
    twoRowBoundaryPairMap q hq hq1 1 (by omega) S r l m l' m' hS hS' hl hm hl' hm'
      (twoVertexTensorProjection n hn l m v) := by
  let V:=quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  let W:=quantumOccupationSpace ℝ (Fin (n+1)) l' ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m'
  let V2:=finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m
  let W2:=finiteWeightSpace (K:=ℝ) l' ⊗[ℝ] finiteWeightSpace (K:=ℝ) m'
  letI : AddCommGroup V:=inferInstance
  letI : Module ℝ V:=inferInstance
  letI : AddCommGroup W:=inferInstance
  letI : Module ℝ W:=inferInstance
  letI : AddCommGroup V2:=inferInstance
  letI : Module ℝ V2:=inferInstance
  letI : AddCommGroup W2:=inferInstance
  letI : Module ℝ W2:=inferInstance
  exact adjoint_boundary_projection_naturality (V:=V) (W:=W) (V₂:=V2) (W₂:=W2)
    (symmetricTensorBilin q n l m) (symmetricTensorBilin q n l' m')
    (quantumTensorBilin q l m) (quantumTensorBilin q l' m')
    (symmetricTensorBilin_symm q n l m) (symmetricTensorBilin_symm q n l' m')
    (twoVertexStandardPairBilin_symm q l m) (twoVertexStandardPairBilin_symm q l' m')
    (quantumTensorBilin_definite q hq l' m')
    (twoVertexTensorEmbedding n hn l m) (twoVertexTensorProjection n hn l m)
    (twoVertexTensorEmbedding n hn l' m') (twoVertexTensorProjection n hn l' m')
    (twoVertexTensorProjection_adjoint q hq hq1 n hn l m)
    (twoVertexTensorProjection_adjoint q hq hq1 n hn l' m')
    (twoRowPairChannelMap q hq hq1 n hn S r l m l' m' hS hS' hl hm hl' hm')
    (twoRowPairBackMap q hq hq1 n hn S r l m l' m' hS hS' hl hm hl' hm')
    (twoRowBoundaryPairMap q hq hq1 1 (by omega) S r l m l' m' hS hS' hl hm hl' hm')
    (twoRowBoundaryBackMap q hq hq1 1 (by omega) S r l m l' m' hS hS' hl hm hl' hm')
    (CompactHighestRealization.channelTransfer_adjoint (V:=V) (W:=W) (ne_of_gt hq)
      (twoRowHighestRealization q hq hq1 n hn S r l m hS hl hm)
      (twoRowHighestRealization q hq hq1 n hn S r l' m' hS' hl' hm'))
    (twoRowBoundaryPairMap_adjoint q hq hq1 1 (by omega) S r l m l' m' hS hS' hl hm hl' hm')
    (fun y =>DFunLike.congr_fun
      (twoRowPairBackMap_boundary_lift q hq hq1 n hn S r l m l' m' hS hS' hl hm hl' hm') y) v

end AMSPhysical
#print axioms AMSPhysical.twoRowPairChannelMap_boundary_projection
