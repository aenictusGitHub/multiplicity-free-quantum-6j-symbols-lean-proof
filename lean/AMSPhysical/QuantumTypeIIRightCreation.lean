import QuantumTypeIITriple
import QuantumMixedCreationIntertwiner
import TypeAHighestSpaceMap

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- Actual adjacent cup creation in the physical Type-II triple. -/
def physicalTypeIIRightCreation (q : ℝ) (n a b c : ℕ) :
    quantumOccupationTripleSpace n a b c →ₗ[ℝ] quantumOccupationTripleSpace n a (b+1) (c+1) :=
  TensorProduct.map LinearMap.id (mixedFiniteCreation q n b c)

theorem physicalTypeIIRightCreation_intertwines (q : ℝ) (hq:q≠0) (hD:q-q⁻¹≠0)
    (n a b c : ℕ) (z:UqTypeA q n) (v:quantumOccupationTripleSpace n a b c) :
    physicalTypeIIRightCreation q n a b c (typeATypeIITriple q hq hD n a b c z v)=
      typeATypeIITriple q hq hD n a (b+1) (c+1) z (physicalTypeIIRightCreation q n a b c v) := by
  let V:=quantumOccupationSpace ℝ (Fin (n+1)) a
  let W:=quantumOccupationSpace ℝ (Fin (n+1)) b ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) c
  let W':=quantumOccupationSpace ℝ (Fin (n+1)) (b+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (c+1)
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  letI : AddCommGroup W' := inferInstance
  letI : Module ℝ W' := inferInstance
  exact typeA_intertwiner_tensor (V:=V) (W:=W) (V':=V) (W':=W') q hq n
    (typeAFiniteQuantumRepresentation q hq hD n a) (typeAMixedTensor q hq hD n b c)
    (typeAFiniteQuantumRepresentation q hq hD n a) (typeAMixedTensor q hq hD n (b+1) (c+1))
    LinearMap.id (mixedFiniteCreation q n b c) (fun _ _=>rfl)
    (mixedFiniteCreation_intertwines q hq hD n b c) z v

def physicalTypeIIHighestRightCreation (q : ℝ) (hq:q≠0) (hD:q-q⁻¹≠0) (n a b c d : ℕ) :
    physicalTypeIIHighestSpace q hq hD n a b c d →ₗ[ℝ]
      physicalTypeIIHighestSpace q hq hD n a (b+1) (c+1) d :=
  typeAHighestSpaceMap q n _ _ (physicalTypeIIRightCreation q n a b c)
    (physicalTypeIIRightCreation_intertwines q hq hD n a b c) (mixedHighestDynkin n d 0)

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIIHighestRightCreation
