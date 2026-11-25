import TensorWeightedHilbert
import CompactTypeAPair

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

theorem typeATensorRepresentation_E_end (q : ℝ) (hq : q≠0) (n : ℕ) (i : Fin n)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W) :
    typeATensorRepresentation q hq n ρ σ (typeAAlgebraGenerator q n i 0)=
      TensorProduct.map (ρ (typeAAlgebraGenerator q n i 0)) (σ (typeAAlgebraGenerator q n i 2))+
        TensorProduct.map 1 (σ (typeAAlgebraGenerator q n i 0)) := by
  apply TensorProduct.ext'
  intro p v
  simp only [typeATensorRepresentation_E,LinearMap.add_apply,TensorProduct.map_tmul,Module.End.one_apply]

theorem typeATensorRepresentation_F_end (q : ℝ) (hq : q≠0) (n : ℕ) (i : Fin n)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W) :
    typeATensorRepresentation q hq n ρ σ (typeAAlgebraGenerator q n i 1)=
      TensorProduct.map (ρ (typeAAlgebraGenerator q n i 1)) 1+
        TensorProduct.map (ρ (typeAAlgebraGenerator q n i 3)) (σ (typeAAlgebraGenerator q n i 1)) := by
  apply TensorProduct.ext'
  intro p v
  simp only [typeATensorRepresentation_F,LinearMap.add_apply,TensorProduct.map_tmul,Module.End.one_apply]

theorem typeATensorRepresentation_K_end (q : ℝ) (hq : q≠0) (n : ℕ) (i : Fin n)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W) :
    typeATensorRepresentation q hq n ρ σ (typeAAlgebraGenerator q n i 2)=
      TensorProduct.map (ρ (typeAAlgebraGenerator q n i 2)) (σ (typeAAlgebraGenerator q n i 2)) := by
  apply TensorProduct.ext'
  intro p v
  exact typeATensorRepresentation_K q hq n ρ σ i p v

theorem typeATensorRepresentation_Ki_end (q : ℝ) (hq : q≠0) (n : ℕ) (i : Fin n)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W) :
    typeATensorRepresentation q hq n ρ σ (typeAAlgebraGenerator q n i 3)=
      TensorProduct.map (ρ (typeAAlgebraGenerator q n i 3)) (σ (typeAAlgebraGenerator q n i 3)) := by
  apply TensorProduct.ext'
  intro p v
  simp [typeATensorRepresentation,typeAQuantumCoproduct_generator,typeACoproductKi,
    Module.endTensorEndAlgHom_apply,TensorProduct.AlgebraTensorModule.map_tmul]

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem compactTypeAPair_tensor (q : ℝ) (hq : q≠0) (n : ℕ)
    (b : Basis ι ℝ V) (c : Basis κ ℝ W) (w : ι → ℝ) (z : κ → ℝ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (hρ : IsCompactTypeAPair q n (finiteWeightedBilin w b.equivFun.toLinearMap) ρ)
    (hσ : IsCompactTypeAPair q n (finiteWeightedBilin z c.equivFun.toLinearMap) σ) :
    IsCompactTypeAPair q n (tensorWeightedBilin b c w z) (typeATensorRepresentation q hq n ρ σ) := by
  have hidV := PairAdjoint.id (finiteWeightedBilin w b.equivFun.toLinearMap)
  have hidW := PairAdjoint.id (finiteWeightedBilin z c.equivFun.toLinearMap)
  have hρinv (i : Fin n) : ρ (typeAAlgebraGenerator q n i 2)*ρ (typeAAlgebraGenerator q n i 3)=1 := by rw [← map_mul,uqA_inverse,map_one]
  have hσinv (i : Fin n) : σ (typeAAlgebraGenerator q n i 2)*σ (typeAAlgebraGenerator q n i 3)=1 := by rw [← map_mul,uqA_inverse,map_one]
  have ht A A' D D' := tensorWeightedBilin_adjoint_map b c w z A A' D D'
  constructor
  · intro i
    rw [typeATensorRepresentation_E_end,typeATensorRepresentation_K_end,typeATensorRepresentation_F_end,
      mul_add,← TensorProduct.map_mul,← TensorProduct.map_mul,hρinv,mul_one]
    exact (ht _ _ _ _ (hρ.adjE i) (hσ.adjK i)).add (ht _ _ _ _ hidV (hσ.adjE i))
  · intro i
    rw [typeATensorRepresentation_F_end,typeATensorRepresentation_E_end,typeATensorRepresentation_Ki_end,
      add_mul,← TensorProduct.map_mul,← TensorProduct.map_mul,hσinv,one_mul]
    exact (ht _ _ _ _ (hρ.adjF i) hidW).add (ht _ _ _ _ (hρ.adjKi i) (hσ.adjF i))
  · intro i
    rw [typeATensorRepresentation_K_end]
    exact ht _ _ _ _ (hρ.adjK i) (hσ.adjK i)
  · intro i
    rw [typeATensorRepresentation_Ki_end]
    exact ht _ _ _ _ (hρ.adjKi i) (hσ.adjKi i)

end AMSPhysical

#print axioms AMSPhysical.compactTypeAPair_tensor
