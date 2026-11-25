import QuantumTypeIILeftBoundary
import TwoVertexTripleProjection

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3600000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def typeIIStandardLeftTreeMap (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    finiteWeightSpace (K:=ℝ) d →ₗ[ℝ]
      (finiteWeightSpace (K:=ℝ) a ⊗[ℝ] (finiteWeightSpace (K:=ℝ) b ⊗[ℝ] finiteWeightSpace (K:=ℝ) c)) :=
  (TensorProduct.assoc ℝ _ _ _).toLinearMap.comp
    (bendRight (W:=finiteWeightSpace (K:=ℝ) a ⊗[ℝ] finiteWeightSpace (K:=ℝ) b)
      (typeIIStandardLeftPairMap q hq hq1 a b c d hbal r) (typeIIStandardBoundaryCup q c))

theorem physicalTypeIILeftTreeMap_eq_bend (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    physicalTypeIILeftTreeMap q hq hq1 n hn a b c d hbal r=
      (TensorProduct.assoc ℝ _ _ _).toLinearMap.comp
        (bendRight (physicalTypeIILeftPairMap q hq hq1 n hn a b c d hbal r) (symmetricCoevaluation q n c)) := by
  rw [symmetricCoevaluation_diagonal]
  rfl

/-- The full actual higher-rank Type-II left tree has the same standard
boundary restriction in EVERY rank, for every output-irrep vector. -/
theorem physicalTypeIILeftTreeMap_boundary (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d)
    (v : finiteWeightSpace (K:=ℝ) d) :
    twoVertexTripleProjection n hn a b c
      (physicalTypeIILeftTreeMap q hq hq1 n hn a b c d hbal r (twoVertexEmbedding n hn d v))=
      typeIIStandardLeftTreeMap q hq hq1 a b c d hbal r v := by
  rw [physicalTypeIILeftTreeMap_eq_bend]
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [twoVertexTripleProjection_assoc,physicalTypeIILeftBent_boundary]
  rfl

/-- Complete actual left highest coupling vectors have a rank-independent
literal two-coordinate boundary. Their actual norms are kept separate. -/
theorem physicalTypeIILeftHighest_boundary (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    twoVertexTripleProjection n hn a b c (physicalTypeIILeftHighest q hq hq1 n hn a b c d hbal r).val=
      typeIIStandardLeftTreeMap q hq hq1 a b c d hbal r (standardWeightBasis (K:=ℝ) d 0) := by
  have he:=physicalTypeIILeftTreeMap_boundary q hq hq1 n hn a b c d hbal r (standardWeightBasis (K:=ℝ) d 0)
  rw [twoVertexEmbedding_basis,twoVertexOccupation_zero] at he
  exact he

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIILeftHighest_boundary
