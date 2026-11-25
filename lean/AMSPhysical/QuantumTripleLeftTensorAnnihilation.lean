import QuantumTripleLeftTensorMetric
import QuantumMixedRawAdjunction
import QuantumFiniteTripleAdjunction
import TensorWeightedAdjunction
import BilinearAdjointTransport

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def finiteTripleLeftTensorAnnihilation (q : ℝ) (n l m c : ℕ) :
    quantumOccupationTripleSpace n (l+1) (m+1) c →ₗ[ℝ] quantumOccupationTripleSpace n l m c :=
  (TensorProduct.assoc ℝ (quantumOccupationSpace ℝ (Fin (n+1)) l)
    (quantumOccupationSpace ℝ (Fin (n+1)) m) (quantumOccupationSpace ℝ (Fin (n+1)) c)).toLinearMap.comp
    ((TensorProduct.map (mixedFiniteRawAnnihilation q n l m) LinearMap.id).comp
      (TensorProduct.assoc ℝ (quantumOccupationSpace ℝ (Fin (n+1)) (l+1))
        (quantumOccupationSpace ℝ (Fin (n+1)) (m+1)) (quantumOccupationSpace ℝ (Fin (n+1)) c)).symm.toLinearMap)

theorem finiteTripleLeftTensorAnnihilation_adjoint (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m c : ℕ)
    (v : quantumOccupationTripleSpace n l m c) (w : quantumOccupationTripleSpace n (l+1) (m+1) c) :
    physicalTripleBilin q n (l+1) (m+1) c (finiteTripleLeftCreation q n l m c v) w=
      physicalTripleBilin q n l m c v (mixedAnnihilationScale q n l m • finiteTripleLeftTensorAnnihilation q n l m c w) := by
  let P := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  let Q := quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1)
  let C := quantumOccupationSpace ℝ (Fin (n+1)) c
  letI : AddCommGroup P := inferInstance
  letI : Module ℝ P := inferInstance
  letI : AddCommGroup Q := inferInstance
  letI : Module ℝ Q := inferInstance
  letI : AddCommGroup C := inferInstance
  letI : Module ℝ C := inferInstance
  letI : AddCommGroup (P ⊗[ℝ] C) := inferInstance
  letI : Module ℝ (P ⊗[ℝ] C) := inferInstance
  letI : AddCommGroup (Q ⊗[ℝ] C) := inferInstance
  letI : Module ℝ (Q ⊗[ℝ] C) := inferInstance
  let V := quantumOccupationTripleSpace n l m c
  let W := quantumOccupationTripleSpace n (l+1) (m+1) c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  have ht : ∀ p z,physicalLeftTripleBilin q n (l+1) (m+1) c
      (TensorProduct.map (mixedFiniteCreation q n l m) LinearMap.id p) z=
      physicalLeftTripleBilin q n l m c p
        (TensorProduct.map (mixedAnnihilationScale q n l m • mixedFiniteRawAnnihilation q n l m) LinearMap.id z) := by
    exact tensorWeightedAdjunction_left (V:=P) (W:=C) (U:=Q)
      ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m))
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) c)
      ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) (l+1)).tensorProduct (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) (m+1)))
      (fun xy =>occupationCompactWeight q n l xy.1*occupationOppositeWeight q n m xy.2)
      (occupationCompactWeight q n c)
      (fun xy =>occupationCompactWeight q n (l+1) xy.1*occupationOppositeWeight q n (m+1) xy.2)
      (mixedFiniteCreation q n l m) (mixedAnnihilationScale q n l m • mixedFiniteRawAnnihilation q n l m)
      (fun p z =>by
        have he:=mixedFiniteRawAnnihilation_adjoint q hq hq1 n l m p z
        unfold mixedTensorBilin tensorWeightedBilin finiteWeightedBilin at he
        exact he)
  have hs:=bilinearAdjoint_transport (V:=P ⊗[ℝ] C) (W:=Q ⊗[ℝ] C) (V':=V) (W':=W)
    (physicalLeftTripleBilin q n l m c) (physicalLeftTripleBilin q n (l+1) (m+1) c)
    (physicalTripleBilin q n l m c) (physicalTripleBilin q n (l+1) (m+1) c)
    (TensorProduct.assoc ℝ _ _ _) (TensorProduct.assoc ℝ _ _ _)
    (physicalTriple_assoc_isometry q n l m c) (physicalTriple_assoc_isometry q n (l+1) (m+1) c)
    (TensorProduct.map (mixedFiniteCreation q n l m) LinearMap.id)
    (TensorProduct.map (mixedAnnihilationScale q n l m • mixedFiniteRawAnnihilation q n l m) LinearMap.id)
    ht v w
  rw [TensorProduct.map_smul_left,LinearMap.smul_apply,map_smul] at hs
  rw [finiteTripleLeftCreation_tensor]
  exact hs

theorem finiteTripleLeftAnnihilation_tensor (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m c : ℕ) :
    finiteTripleLeftAnnihilation q n l m c=finiteTripleLeftTensorAnnihilation q n l m c := by
  let V := quantumOccupationTripleSpace n l m c
  let W := quantumOccupationTripleSpace n (l+1) (m+1) c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  have he:=bilinearAdjoint_unique (V:=V) (W:=W)
    (physicalTripleBilin q n l m c) (physicalTripleBilin_definite q hq n l m c)
    (physicalTripleBilin_symm q n l m c) (physicalTripleBilin q n (l+1) (m+1) c)
    (finiteTripleLeftCreation q n l m c)
    (mixedAnnihilationScale q n l m • finiteTripleLeftAnnihilation q n l m c)
    (mixedAnnihilationScale q n l m • finiteTripleLeftTensorAnnihilation q n l m c)
    (finiteTripleLeftAnnihilation_adjoint q hq hq1 n l m c)
    (finiteTripleLeftTensorAnnihilation_adjoint q hq hq1 n l m c)
  exact smul_right_injective _ (ne_of_gt (mixedAnnihilationScale_pos q hq hq1 n l m)) he

end AMSPhysical
#print axioms AMSPhysical.finiteTripleLeftAnnihilation_tensor
