import QuantumMixedReflection
import QuantumMixedCreationIntertwiner
import QuantumOccupationUnitWeights
import InvolutiveTwistedIntertwiner

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem mixedReflection_inverse_intertwines (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ)
    (z : UqTypeA q n)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :
    (mixedReflection n l m).symm (typeAReverseMixedTensor q hq hD n l m z v)=
      typeAMixedTensor q hq hD n l m (typeADynkinReflection q n z) ((mixedReflection n l m).symm v) := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact inverse_involutiveTwistedIntertwiner (V:=V) (W:=V)
    (typeAMixedTensor q hq hD n l m) (typeAReverseMixedTensor q hq hD n l m)
    (typeADynkinReflection q n) (typeADynkinReflection_involutive q n) (mixedReflection n l m)
    (mixedReflection_intertwines q hq hD n l m) z v

def reverseMixedFiniteCreation (q : ℝ) (n l m : ℕ) :
    (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) →ₗ[ℝ]
      (quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1)) :=
  (mixedReflection n (l+1) (m+1)).toLinearMap.comp
    ((mixedFiniteCreation q n l m).comp (mixedReflection n l m).symm.toLinearMap)

theorem reverseMixedFiniteCreation_intertwines (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ)
    (z : UqTypeA q n)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :
    reverseMixedFiniteCreation q n l m (typeAReverseMixedTensor q hq hD n l m z v)=
      typeAReverseMixedTensor q hq hD n (l+1) (m+1) z (reverseMixedFiniteCreation q n l m v) := by
  unfold reverseMixedFiniteCreation
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [mixedReflection_inverse_intertwines q hq hD,mixedFiniteCreation_intertwines q hq hD,
    mixedReflection_intertwines q hq hD,typeADynkinReflection_involutive]

theorem mixedReflection_basis (n l m : ℕ) (x : occupationWeights (Fin (n+1)) l) (y : occupationWeights (Fin (n+1)) m) :
    mixedReflection n l m (quantumOccupationBasis (K:=ℝ) l x ⊗ₜ[ℝ] quantumOccupationBasis (K:=ℝ) m y)=
      quantumOccupationBasis (K:=ℝ) l (occupationReflection n l x) ⊗ₜ[ℝ]
        quantumOccupationBasis (K:=ℝ) m (occupationReflection n m y) := by
  simp only [mixedReflection,TensorProduct.congr_tmul,quantumOccupationReflection_basis]

theorem mixedReflection_inverse_basis (n l m : ℕ) (x : occupationWeights (Fin (n+1)) l) (y : occupationWeights (Fin (n+1)) m) :
    (mixedReflection n l m).symm (quantumOccupationBasis (K:=ℝ) l x ⊗ₜ[ℝ] quantumOccupationBasis (K:=ℝ) m y)=
      quantumOccupationBasis (K:=ℝ) l (occupationReflection n l x) ⊗ₜ[ℝ]
        quantumOccupationBasis (K:=ℝ) m (occupationReflection n m y) := by
  apply (mixedReflection n l m).injective
  rw [LinearEquiv.apply_symm_apply,mixedReflection_basis,occupationReflection_involutive,occupationReflection_involutive]

end AMSPhysical
#print axioms AMSPhysical.reverseMixedFiniteCreation_intertwines
