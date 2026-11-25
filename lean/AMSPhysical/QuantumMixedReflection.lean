import QuantumOppositeReflection
import QuantumReflectionMetric
import QuantumDynkinTensor
import QuantumTypeATensorIntertwiner
import QuantumReverseMixedTensor
import TensorWeightedIsometries

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 180000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def mixedReflection (n l m : ℕ) :
    (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) ≃ₗ[ℝ]
      (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :=
  TensorProduct.congr (quantumOccupationReflection n l) (quantumOccupationReflection n m)

theorem mixedReflection_intertwines (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ)
    (z : UqTypeA q n)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :
    mixedReflection n l m (typeAMixedTensor q hq hD n l m z v)=
      typeAReverseMixedTensor q hq hD n l m (typeADynkinReflection q n z) (mixedReflection n l m v) := by
  have h:=typeA_intertwiner_tensor q hq n
    (typeAFiniteQuantumRepresentation q hq hD n l) (typeAOppositeSymmetricRepresentation q hq hD n m)
    ((typeAOppositeSymmetricRepresentation q hq hD n l).comp (typeADynkinReflection q n))
    ((typeAFiniteQuantumRepresentation q hq hD n m).comp (typeADynkinReflection q n))
    (quantumOccupationReflection n l).toLinearMap (quantumOccupationReflection n m).toLinearMap
    (quantumOccupationReflection_intertwines q hq hD n l)
    (quantumOccupationReflection_opposite_intertwines q hq hD n m) z v
  rw [typeATensorRepresentation_dynkin] at h
  exact h

theorem mixedReflection_isometry (q : ℝ) (hq : q≠0) (n l m : ℕ)
    (v w : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :
    reverseMixedTensorBilin q n l m (mixedReflection n l m v) (mixedReflection n l m w)=
      mixedTensorBilin q n l m v w := by
  exact tensorWeightedBilin_map_isometry
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l) (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l) (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)
    (occupationCompactWeight q n l) (occupationOppositeWeight q n m)
    (occupationOppositeWeight q n l) (occupationCompactWeight q n m)
    (quantumOccupationReflection n l).toLinearMap (quantumOccupationReflection n m).toLinearMap
    (quantumOccupationReflection_compact_isometry q hq n l)
    (quantumOccupationReflection_opposite_isometry q hq n m) v w

end AMSPhysical
#print axioms AMSPhysical.mixedReflection_intertwines
