import StandardClebschAtLabel
import TwoRowRootStringsTotal
import TwoVertexPairProjection

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def standardClebschAtTotal (q:ℝ) (hq:0<q) (hq1:q≠1) (S r l m:ℕ)
    (hS:l+m=S) (hl:r≤l) (hm:r≤m) :
    finiteWeightSpace (K:=ℝ) (S-2*r) →ₗ[ℝ] (finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) :=
  standardClebschAtLabel q hq hq1 l m ⟨r,by omega⟩ (S-2*r) (by change l+m-2*r=S-2*r;omega)

theorem standardClebschAtTotal_embedding (q:ℝ) (hq:0<q) (hq1:q≠1) (n:ℕ) (hn:0<n)
    (S r l m:ℕ) (hS:l+m=S) (hl:r≤l) (hm:r≤m) (v:finiteWeightSpace (K:=ℝ) (S-2*r)) :
    twoVertexTensorEmbedding n hn l m (standardClebschAtTotal q hq hq1 S r l m hS hl hm v)=
      twoRowRootStringAtTotal q hq hq1 n hn S r l m hS hl hm v := by
  subst S
  rfl

theorem twoRowRootStringAtTotal_projection (q:ℝ) (hq:0<q) (hq1:q≠1) (n:ℕ) (hn:0<n)
    (S r l m:ℕ) (hS:l+m=S) (hl:r≤l) (hm:r≤m) (v:finiteWeightSpace (K:=ℝ) (S-2*r)) :
    twoVertexTensorProjection n hn l m (twoRowRootStringAtTotal q hq hq1 n hn S r l m hS hl hm v)=
      standardClebschAtTotal q hq hq1 S r l m hS hl hm v := by
  rw [← standardClebschAtTotal_embedding,twoVertexTensorProjection_embedding]

end AMSPhysical
#print axioms AMSPhysical.twoRowRootStringAtTotal_projection
