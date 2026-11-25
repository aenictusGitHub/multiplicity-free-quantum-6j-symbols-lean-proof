import QuantumReverseRawSpectrum
import QuantumTypeATripleCompact
import QuantumFiniteTripleAdjunction
import TensorWeightedAdjunction

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem finiteTripleRightTensorAnnihilation_adjoint (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m c : ℕ)
    (v : quantumOccupationTripleSpace n l m c) (w : quantumOccupationTripleSpace n l (m+1) (c+1)) :
    physicalTripleBilin q n l (m+1) (c+1) (finiteTripleRightCreation q n l m c v) w=
      physicalTripleBilin q n l m c v (mixedAnnihilationScale q n m c •
        TensorProduct.map LinearMap.id (reverseMixedRawAnnihilation q n m c) w) := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l
  let W := quantumOccupationSpace ℝ (Fin (n+1)) m ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) c
  let U := quantumOccupationSpace ℝ (Fin (n+1)) (m+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (c+1)
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  letI : AddCommGroup U := inferInstance
  letI : Module ℝ U := inferInstance
  have ht:=tensorWeightedAdjunction_right (V:=V) (W:=W) (U:=U)
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l)
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m).tensorProduct (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) c))
    ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) (m+1)).tensorProduct (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) (c+1)))
    (occupationCompactWeight q n l)
    (fun yz =>occupationOppositeWeight q n m yz.1*occupationCompactWeight q n c yz.2)
    (fun yz =>occupationOppositeWeight q n (m+1) yz.1*occupationCompactWeight q n (c+1) yz.2)
    (reverseMixedFiniteCreation q n m c) (mixedAnnihilationScale q n m c • reverseMixedRawAnnihilation q n m c)
    (fun p z =>by
      have he:=reverseMixedRawAnnihilation_adjoint q hq hq1 n m c p z
      unfold reverseMixedTensorBilin tensorWeightedBilin finiteWeightedBilin at he
      exact he) v w
  rw [TensorProduct.map_smul_right,LinearMap.smul_apply] at ht
  rw [finiteTripleRightCreation_tensor,physicalTripleBilin_tensor,physicalTripleBilin_tensor]
  exact ht

/-- The literal finite occupation annihilator is exactly the tensor product
of the identity with the reflected physical pair annihilator. -/
theorem finiteTripleRightAnnihilation_tensor (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m c : ℕ) :
    finiteTripleRightAnnihilation q n l m c=
      TensorProduct.map (LinearMap.id : Module.End ℝ (quantumOccupationSpace ℝ (Fin (n+1)) l))
        (reverseMixedRawAnnihilation q n m c) := by
  let V := quantumOccupationTripleSpace n l m c
  let W := quantumOccupationTripleSpace n l (m+1) (c+1)
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  have he:=bilinearAdjoint_unique (V:=V) (W:=W)
    (physicalTripleBilin q n l m c) (physicalTripleBilin_definite q hq n l m c)
    (physicalTripleBilin_symm q n l m c) (physicalTripleBilin q n l (m+1) (c+1))
    (finiteTripleRightCreation q n l m c)
    (mixedAnnihilationScale q n m c • finiteTripleRightAnnihilation q n l m c)
    (mixedAnnihilationScale q n m c • TensorProduct.map (LinearMap.id : Module.End ℝ (quantumOccupationSpace ℝ (Fin (n+1)) l)) (reverseMixedRawAnnihilation q n m c))
    (finiteTripleRightAnnihilation_adjoint q hq hq1 n l m c)
    (finiteTripleRightTensorAnnihilation_adjoint q hq hq1 n l m c)
  exact smul_right_injective _ (ne_of_gt (mixedAnnihilationScale_pos q hq hq1 n m c)) he

end AMSPhysical
#print axioms AMSPhysical.finiteTripleRightAnnihilation_tensor
