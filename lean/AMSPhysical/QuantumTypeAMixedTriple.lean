import OccupationTripleCoefficients
import QuantumReverseMixedTensor
import QuantumTypeAAssociatorInverse
import QuantumReverseCreationBasis
import QuantumFiniteTripleCreation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def typeAMixedTriple (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m c : ℕ) :
    UqTypeA q n →ₐ[ℝ] Module.End ℝ (quantumOccupationTripleSpace n l m c) := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l
  let W := quantumOccupationSpace ℝ (Fin (n+1)) m ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  exact typeATensorRepresentation (V:=V) (W:=W) q hq n (typeAFiniteQuantumRepresentation q hq hD n l)
    (typeAReverseMixedTensor q hq hD n m c)

theorem occupationTripleBasis_apply (n l m c : ℕ) (p : OccupationTripleIndex n l m c) :
    occupationTripleBasis n l m c p=quantumOccupationBasis (K:=ℝ) l p.1 ⊗ₜ[ℝ]
      (quantumOccupationBasis (K:=ℝ) m p.2.1 ⊗ₜ[ℝ] quantumOccupationBasis (K:=ℝ) c p.2.2) := by
  unfold occupationTripleBasis
  rw [Module.Basis.tensorProduct_apply',Module.Basis.tensorProduct_apply']

theorem finiteTripleRightCreation_tensor (q : ℝ) (n l m c : ℕ) :
    finiteTripleRightCreation q n l m c=
      TensorProduct.map (LinearMap.id : Module.End ℝ (quantumOccupationSpace ℝ (Fin (n+1)) l))
        (reverseMixedFiniteCreation q n m c) := by
  apply (occupationTripleBasis n l m c).ext
  intro p
  rw [finiteTripleRightCreation_basis]
  simp only [occupationTripleBasis_apply,TensorProduct.map_tmul,
    LinearMap.id_apply,reverseMixedFiniteCreation_basis,TensorProduct.tmul_sum,TensorProduct.tmul_smul]
  rfl

theorem finiteTripleLeftCreation_tensor (q : ℝ) (n l m c : ℕ) :
    finiteTripleLeftCreation q n l m c=
      (TensorProduct.assoc ℝ (quantumOccupationSpace ℝ (Fin (n+1)) (l+1))
        (quantumOccupationSpace ℝ (Fin (n+1)) (m+1)) (quantumOccupationSpace ℝ (Fin (n+1)) c)).toLinearMap.comp
        ((TensorProduct.map (mixedFiniteCreation q n l m)
          (LinearMap.id : Module.End ℝ (quantumOccupationSpace ℝ (Fin (n+1)) c))).comp
          (TensorProduct.assoc ℝ (quantumOccupationSpace ℝ (Fin (n+1)) l)
            (quantumOccupationSpace ℝ (Fin (n+1)) m) (quantumOccupationSpace ℝ (Fin (n+1)) c)).symm.toLinearMap) := by
  apply (occupationTripleBasis n l m c).ext
  intro p
  rw [finiteTripleLeftCreation_basis]
  simp only [occupationTripleBasis_apply,LinearMap.comp_apply,LinearEquiv.coe_coe,
    TensorProduct.assoc_symm_tmul,TensorProduct.map_tmul,LinearMap.id_apply,mixedFiniteCreation_basis,
    TensorProduct.sum_tmul,TensorProduct.smul_tmul',map_sum,map_smul,TensorProduct.assoc_tmul]
  rfl

end AMSPhysical
