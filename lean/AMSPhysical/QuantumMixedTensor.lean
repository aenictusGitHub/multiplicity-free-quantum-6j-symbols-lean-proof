import QuantumOccupationShiftActions
import QuantumTypeADualSymmetric
import QuantumTypeATensorRepresentation
import QuantumMixedCoefficient

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- The actual mixed symmetric/opposite-symmetric tensor representation. -/
def typeAMixedTensor (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m : ℕ) :
    UqTypeA q n →ₐ[ℝ] Module.End ℝ
      (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :=
  typeATensorRepresentation q hq n (typeAFiniteQuantumRepresentation q hq hD n l)
    (typeAOppositeSymmetricRepresentation q hq hD n m)

def mixedOccupationTensor (n r a b : ℕ) (t : occupationWeights (Fin (n+1)) r) :
    quantumOccupationSpace ℝ (Fin (n+1)) (r+a) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (r+b) :=
  quantumOccupationBasis (K:=ℝ) (r+a) (shiftedOccupation n r a 0 t) ⊗ₜ[ℝ]
    quantumOccupationBasis (K:=ℝ) (r+b) (shiftedOccupation n r b (Fin.last n) t)

def mixedHighestVector (q : ℝ) (n r a b : ℕ) :
    quantumOccupationSpace ℝ (Fin (n+1)) (r+a) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (r+b) :=
  ∑ t : occupationWeights (Fin (n+1)) r,mixedHighestCoefficient q n r b t • mixedOccupationTensor n r a b t

def mixedFirstRaising (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n r a b : ℕ) (i : Fin n)
    (t : occupationWeights (Fin (n+1)) r) :
    quantumOccupationSpace ℝ (Fin (n+1)) (r+a) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (r+b) :=
  mixedHighestCoefficient q n r b t •
    (typeAFiniteGenerator q hq hD n (r+a) i 0
      (quantumOccupationBasis (K:=ℝ) (r+a) (shiftedOccupation n r a 0 t)) ⊗ₜ[ℝ]
    typeAFiniteGenerator q hq hD n (r+b) i 3
      (quantumOccupationBasis (K:=ℝ) (r+b) (shiftedOccupation n r b (Fin.last n) t)))

def mixedSecondRaising (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n r a b : ℕ) (i : Fin n)
    (t : occupationWeights (Fin (n+1)) r) :
    quantumOccupationSpace ℝ (Fin (n+1)) (r+a) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (r+b) :=
  mixedHighestCoefficient q n r b t •
    (quantumOccupationBasis (K:=ℝ) (r+a) (shiftedOccupation n r a 0 t) ⊗ₜ[ℝ]
    typeAFiniteGenerator q hq hD n (r+b) i 1
      (quantumOccupationBasis (K:=ℝ) (r+b) (shiftedOccupation n r b (Fin.last n) t)))

theorem mixedHighestVector_E_sum (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n r a b : ℕ) (i : Fin n) :
    typeAMixedTensor q hq hD n (r+a) (r+b) (typeAAlgebraGenerator q n i 0) (mixedHighestVector q n r a b)=
      (∑ t : occupationWeights (Fin (n+1)) r,mixedFirstRaising q hq hD n r a b i t)+
      (∑ t : occupationWeights (Fin (n+1)) r,mixedSecondRaising q hq hD n r a b i t) := by
  unfold mixedHighestVector
  rw [map_sum]
  simp only [map_smul]
  have he (t : occupationWeights (Fin (n+1)) r) :
      typeAMixedTensor q hq hD n (r+a) (r+b) (typeAAlgebraGenerator q n i 0) (mixedOccupationTensor n r a b t)=
        typeAFiniteGenerator q hq hD n (r+a) i 0
          (quantumOccupationBasis (K:=ℝ) (r+a) (shiftedOccupation n r a 0 t)) ⊗ₜ[ℝ]
        typeAFiniteGenerator q hq hD n (r+b) i 3
          (quantumOccupationBasis (K:=ℝ) (r+b) (shiftedOccupation n r b (Fin.last n) t))+
        quantumOccupationBasis (K:=ℝ) (r+a) (shiftedOccupation n r a 0 t) ⊗ₜ[ℝ]
        typeAFiniteGenerator q hq hD n (r+b) i 1
          (quantumOccupationBasis (K:=ℝ) (r+b) (shiftedOccupation n r b (Fin.last n) t)) := by
    simp [typeAMixedTensor,mixedOccupationTensor,typeATensorRepresentation,typeAQuantumCoproduct_generator,
      typeACoproductE,typeAOpposite_generator,Module.endTensorEndAlgHom_apply,
      TensorProduct.AlgebraTensorModule.map_tmul,typeAFiniteGenerator]
  simp only [he,smul_add,Finset.sum_add_distrib,mixedFirstRaising,mixedSecondRaising]

end AMSPhysical
#print axioms AMSPhysical.mixedHighestVector_E_sum
