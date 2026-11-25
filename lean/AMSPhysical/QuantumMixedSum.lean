import QuantumMixedTensor
import TensorBasisSlices

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def mixedTensorSum (n r a b : ℕ) (f : occupationWeights (Fin (n+1)) r → ℝ) :
    quantumOccupationSpace ℝ (Fin (n+1)) (r+a) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (r+b) :=
  ∑ t : occupationWeights (Fin (n+1)) r,f t • mixedOccupationTensor n r a b t

theorem mixedTensorSum_E_sum (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n r a b : ℕ) (i : Fin n) (f : occupationWeights (Fin (n+1)) r → ℝ) :
    typeAMixedTensor q hq hD n (r+a) (r+b) (typeAAlgebraGenerator q n i 0) (mixedTensorSum n r a b f)=
      (∑ t : occupationWeights (Fin (n+1)) r,f t •
        (typeAFiniteGenerator q hq hD n (r+a) i 0
          (quantumOccupationBasis (K:=ℝ) (r+a) (shiftedOccupation n r a 0 t)) ⊗ₜ[ℝ]
        typeAFiniteGenerator q hq hD n (r+b) i 3
          (quantumOccupationBasis (K:=ℝ) (r+b) (shiftedOccupation n r b (Fin.last n) t))))+
      (∑ t : occupationWeights (Fin (n+1)) r,f t •
        (quantumOccupationBasis (K:=ℝ) (r+a) (shiftedOccupation n r a 0 t) ⊗ₜ[ℝ]
        typeAFiniteGenerator q hq hD n (r+b) i 1
          (quantumOccupationBasis (K:=ℝ) (r+b) (shiftedOccupation n r b (Fin.last n) t)))) := by
  unfold mixedTensorSum
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
  simp only [he,smul_add,Finset.sum_add_distrib]

end AMSPhysical
#print axioms AMSPhysical.mixedTensorSum_E_sum
