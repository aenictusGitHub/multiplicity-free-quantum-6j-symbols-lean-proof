import TwoRowBoundaryProjection
import TwoVertexCupProjection
import FiniteBendingNaturality
import QuantumTypeIILeftTree
import QuantumTripleMetric

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3600000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def typeIIStandardLeftPairMap (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    (finiteWeightSpace (K:=ℝ) d ⊗[ℝ] finiteWeightSpace (K:=ℝ) c) →ₗ[ℝ]
      (finiteWeightSpace (K:=ℝ) a ⊗[ℝ] finiteWeightSpace (K:=ℝ) b) :=
  twoRowBoundaryPairMap q hq hq1 1 (by omega) (a+b) r.val d c a b (by omega) rfl
    (by have h:=r.isLt;omega) (by have h:=r.isLt;omega)
    (by have h:=r.isLt;omega) (by have h:=r.isLt;omega)

def typeIIStandardBoundaryCup (q : ℝ) (c : ℕ) :=
  diagonalCoevaluation (standardWeightBasis (K:=ℝ) c)
    (fun k =>(-1:ℝ)^(k.val:ℤ)/quantumWeight q c k.val)

theorem physicalTypeIILeftPairMap_boundary_projection (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) d ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) c) :
    twoVertexTensorProjection n hn a b (physicalTypeIILeftPairMap q hq hq1 n hn a b c d hbal r v)=
      typeIIStandardLeftPairMap q hq hq1 a b c d hbal r (twoVertexTensorProjection n hn d c v) :=
  twoRowPairChannelMap_boundary_projection q hq hq1 n hn (a+b) r.val d c a b (by omega) rfl
    (by have h:=r.isLt;omega) (by have h:=r.isLt;omega)
    (by have h:=r.isLt;omega) (by have h:=r.isLt;omega) v

theorem physicalTypeIILeftBent_boundary (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d)
    (v : finiteWeightSpace (K:=ℝ) d) :
    TensorProduct.map (twoVertexTensorProjection n hn a b) (twoVertexProjection n hn c)
      (bendRight (physicalTypeIILeftPairMap q hq hq1 n hn a b c d hbal r)
        (symmetricCoevaluation q n c) (twoVertexEmbedding n hn d v))=
      bendRight (W:=finiteWeightSpace (K:=ℝ) a ⊗[ℝ] finiteWeightSpace (K:=ℝ) b) (typeIIStandardLeftPairMap q hq hq1 a b c d hbal r) (typeIIStandardBoundaryCup q c) v := by
  exact bendRight_projection_naturality
    (X:=quantumOccupationSpace ℝ (Fin (n+1)) d) (V:=quantumOccupationSpace ℝ (Fin (n+1)) c)
    (W:=quantumOccupationSpace ℝ (Fin (n+1)) a ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) b)
    (X₂:=finiteWeightSpace (K:=ℝ) d) (V₂:=finiteWeightSpace (K:=ℝ) c)
    (W₂:=finiteWeightSpace (K:=ℝ) a ⊗[ℝ] finiteWeightSpace (K:=ℝ) b)
    (physicalTypeIILeftPairMap q hq hq1 n hn a b c d hbal r)
    (typeIIStandardLeftPairMap q hq hq1 a b c d hbal r)
    (twoVertexEmbedding n hn d) (twoVertexProjection n hn d) (twoVertexProjection n hn c)
    (twoVertexTensorProjection n hn a b) (twoVertexProjection_embedding n hn d)
    (physicalTypeIILeftPairMap_boundary_projection q hq hq1 n hn a b c d hbal r)
    (symmetricCoevaluation q n c) (typeIIStandardBoundaryCup q c)
    (symmetricCoevaluation_twoVertex_projection q hq hq1 n hn c) v

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIILeftBent_boundary
