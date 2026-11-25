import TwoVertexProjectionAdjoint
import TwoRowRootStringsTotal

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def twoVertexTensorProjection (n : ℕ) (hn : 0<n) (l m : ℕ) :
    (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) →ₗ[ℝ]
      (finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) :=
  TensorProduct.map (twoVertexProjection n hn l) (twoVertexProjection n hn m)

theorem twoVertexTensorProjection_embedding (n : ℕ) (hn : 0<n) (l m : ℕ)
    (v : finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) :
    twoVertexTensorProjection n hn l m (twoVertexTensorEmbedding n hn l m v)=v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw => simp only [map_add,hv,hw]
  | tmul v w =>
    change TensorProduct.map _ _ (TensorProduct.map _ _ (v ⊗ₜ[ℝ] w))=_
    simp only [TensorProduct.map_tmul,twoVertexProjection_embedding]

theorem twoVertexTensorProjection_rootString (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : TwoRowFusionIndex l m)
    (v : finiteWeightSpace (K:=ℝ) (coupledLabel l m r)) :
    twoVertexTensorProjection n hn l m (twoRowRootStringEmbedding q hq hq1 n hn l m r v)=
      unitaryQuantumClebschMap q hq hq1 l m r v :=
  twoVertexTensorProjection_embedding n hn l m _

theorem twoVertexTensorProjection_rootString_total_rank_independent (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (S r l m : ℕ) (hS : l+m=S) (hl : r≤l) (hm : r≤m)
    (v : finiteWeightSpace (K:=ℝ) (S-2*r)) :
    twoVertexTensorProjection n hn l m (twoRowRootStringAtTotal q hq hq1 n hn S r l m hS hl hm v)=
    twoVertexTensorProjection 1 (by omega) l m
      (twoRowRootStringAtTotal q hq hq1 1 (by omega) S r l m hS hl hm v) := by
  subst S
  change twoVertexTensorProjection n hn l m
    (twoRowRootStringEmbedding q hq hq1 n hn l m ⟨r,by omega⟩ v)=
      twoVertexTensorProjection 1 (by omega) l m
        (twoRowRootStringEmbedding q hq hq1 1 (by omega) l m ⟨r,by omega⟩ v)
  rw [twoVertexTensorProjection_rootString,twoVertexTensorProjection_rootString]

end AMSPhysical
#print axioms AMSPhysical.twoVertexTensorProjection_rootString_total_rank_independent
