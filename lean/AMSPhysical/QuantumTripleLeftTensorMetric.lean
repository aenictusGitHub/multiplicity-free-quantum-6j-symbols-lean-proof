import QuantumTypeATripleCompact
import TensorWeightedIsometries

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def physicalLeftTripleBilin (q : ℝ) (n l m c : ℕ) :
    ((quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) ⊗[ℝ]
      quantumOccupationSpace ℝ (Fin (n+1)) c) →ₗ[ℝ]
    ((quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) ⊗[ℝ]
      quantumOccupationSpace ℝ (Fin (n+1)) c) →ₗ[ℝ] ℝ := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  let W := quantumOccupationSpace ℝ (Fin (n+1)) c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  exact tensorWeightedBilin (V:=V) (W:=W)
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m))
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) c)
    (fun xy : occupationWeights (Fin (n+1)) l × occupationWeights (Fin (n+1)) m =>occupationCompactWeight q n l xy.1*occupationOppositeWeight q n m xy.2)
    (occupationCompactWeight q n c)

theorem physicalTriple_assoc_isometry (q : ℝ) (n l m c : ℕ)
    (v w : (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) ⊗[ℝ]
      quantumOccupationSpace ℝ (Fin (n+1)) c) :
    physicalTripleBilin q n l m c ((TensorProduct.assoc ℝ _ _ _) v) ((TensorProduct.assoc ℝ _ _ _) w)=
      physicalLeftTripleBilin q n l m c v w := by
  rw [physicalTripleBilin_tensor]
  exact tensorWeightedBilin_assoc_isometry
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l)
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) c)
    (occupationCompactWeight q n l) (occupationOppositeWeight q n m) (occupationCompactWeight q n c) v w

theorem physicalTriple_assoc_symm_isometry (q : ℝ) (n l m c : ℕ)
    (v w : quantumOccupationTripleSpace n l m c) :
    physicalLeftTripleBilin q n l m c ((TensorProduct.assoc ℝ _ _ _).symm v) ((TensorProduct.assoc ℝ _ _ _).symm w)=
      physicalTripleBilin q n l m c v w := by
  have he:=physicalTriple_assoc_isometry q n l m c
    ((TensorProduct.assoc ℝ _ _ _).symm v) ((TensorProduct.assoc ℝ _ _ _).symm w)
  rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply] at he
  exact he.symm

end AMSPhysical
#print axioms AMSPhysical.physicalTriple_assoc_isometry
