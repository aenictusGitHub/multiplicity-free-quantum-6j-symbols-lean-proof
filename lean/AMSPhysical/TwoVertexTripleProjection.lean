import TwoVertexPairProjection
import QuantumPhysicalTripleInstances

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def twoVertexTripleProjection (n : ℕ) (hn : 0<n) (a b c : ℕ) :
    quantumOccupationTripleSpace n a b c →ₗ[ℝ]
      (finiteWeightSpace (K:=ℝ) a ⊗[ℝ] (finiteWeightSpace (K:=ℝ) b ⊗[ℝ] finiteWeightSpace (K:=ℝ) c)) :=
  TensorProduct.map (twoVertexProjection n hn a) (twoVertexTensorProjection n hn b c)

theorem twoVertexTripleProjection_assoc (n : ℕ) (hn : 0<n) (a b c : ℕ)
    (w : (quantumOccupationSpace ℝ (Fin (n+1)) a ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) b) ⊗[ℝ]
      quantumOccupationSpace ℝ (Fin (n+1)) c) :
    twoVertexTripleProjection n hn a b c ((TensorProduct.assoc ℝ _ _ _) w)=
      (TensorProduct.assoc ℝ _ _ _)
        (TensorProduct.map (twoVertexTensorProjection n hn a b) (twoVertexProjection n hn c) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w z hw hz => simp only [map_add,hw,hz]
  | tmul u v =>
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add u u' hu hu' => simp only [TensorProduct.add_tmul,map_add,hu,hu']
    | tmul x y =>
      simp only [TensorProduct.assoc_tmul,twoVertexTripleProjection,twoVertexTensorProjection,TensorProduct.map_tmul]

end AMSPhysical
#print axioms AMSPhysical.twoVertexTripleProjection_assoc
