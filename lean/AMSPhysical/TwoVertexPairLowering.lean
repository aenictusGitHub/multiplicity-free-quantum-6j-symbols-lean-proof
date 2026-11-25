import TwoVertexFullIntertwiner
import TwoVertexTensorEmbedding

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem twoVertexTensorEmbedding_F (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (v : finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) :
    twoVertexTensorEmbedding n hn l m (finiteTensorRepresentation q hq hD l m (uqGenerator q 1) v)=
      typeASymmetricTensor q hq hD n l m (typeAAlgebraGenerator q n (⟨0,hn⟩ : Fin n) 1)
        (twoVertexTensorEmbedding n hn l m v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw => simp only [map_add,hv,hw]
  | tmul v w =>
    have he : finiteTensorRepresentation q hq hD l m (uqGenerator q 1) (v ⊗ₜ[ℝ] w)=
        finiteQuantumF q l v ⊗ₜ[ℝ] w+finiteQuantumKinv q l v ⊗ₜ[ℝ] finiteQuantumF q m w := by
      simpa [finiteTensorRepresentation,uqGenerator,finiteQuantumRepresentation_generator] using
        tensorRepresentation_F q hq (finiteQuantumRepresentation q hq hD l)
          (finiteQuantumRepresentation q hq hD m) v w
    rw [he,map_add]
    simp only [twoVertexTensorEmbedding,TensorProduct.map_tmul]
    rw [twoVertexEmbedding_F,twoVertexEmbedding_Kinv,twoVertexEmbedding_F]
    symm
    exact typeATensorRepresentation_F q hq n
      (typeAFiniteQuantumRepresentation q hq hD n l) (typeAFiniteQuantumRepresentation q hq hD n m)
      (⟨0,hn⟩ : Fin n) _ _

end AMSPhysical
#print axioms AMSPhysical.twoVertexTensorEmbedding_F
