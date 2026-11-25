import TensorWeightedHilbert
import CompactQuantumPair

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

theorem tensorRepresentation_E_end (q : ℝ) (hq : q≠0)
    (ρ : UqSL2 q →ₐ[ℝ] Module.End ℝ V) (σ : UqSL2 q →ₐ[ℝ] Module.End ℝ W) :
    tensorRepresentation q hq ρ σ (uqGenerator q 0)=
      TensorProduct.map (ρ (uqGenerator q 0)) (σ (uqGenerator q 2))+
        TensorProduct.map 1 (σ (uqGenerator q 0)) := by
  apply TensorProduct.ext'
  intro p v
  simp only [tensorRepresentation_E,LinearMap.add_apply,TensorProduct.map_tmul,Module.End.one_apply]

theorem tensorRepresentation_F_end (q : ℝ) (hq : q≠0)
    (ρ : UqSL2 q →ₐ[ℝ] Module.End ℝ V) (σ : UqSL2 q →ₐ[ℝ] Module.End ℝ W) :
    tensorRepresentation q hq ρ σ (uqGenerator q 1)=
      TensorProduct.map (ρ (uqGenerator q 1)) 1+
        TensorProduct.map (ρ (uqGenerator q 3)) (σ (uqGenerator q 1)) := by
  apply TensorProduct.ext'
  intro p v
  simp only [tensorRepresentation_F,LinearMap.add_apply,TensorProduct.map_tmul,Module.End.one_apply]

theorem tensorRepresentation_K_end (q : ℝ) (hq : q≠0)
    (ρ : UqSL2 q →ₐ[ℝ] Module.End ℝ V) (σ : UqSL2 q →ₐ[ℝ] Module.End ℝ W) :
    tensorRepresentation q hq ρ σ (uqGenerator q 2)=
      TensorProduct.map (ρ (uqGenerator q 2)) (σ (uqGenerator q 2)) := by
  apply TensorProduct.ext'
  intro p v
  exact tensorRepresentation_K q hq ρ σ p v

theorem tensorRepresentation_Ki_end (q : ℝ) (hq : q≠0)
    (ρ : UqSL2 q →ₐ[ℝ] Module.End ℝ V) (σ : UqSL2 q →ₐ[ℝ] Module.End ℝ W) :
    tensorRepresentation q hq ρ σ (uqGenerator q 3)=
      TensorProduct.map (ρ (uqGenerator q 3)) (σ (uqGenerator q 3)) := by
  apply TensorProduct.ext'
  intro p v
  simp [tensorRepresentation,quantumCoproduct_generator,coproductKinv,
    Module.endTensorEndAlgHom_apply,TensorProduct.AlgebraTensorModule.map_tmul]

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem compactQuantumPair_tensor (q : ℝ) (hq : q≠0)
    (b : Basis ι ℝ V) (c : Basis κ ℝ W) (w : ι → ℝ) (z : κ → ℝ)
    (ρ : UqSL2 q →ₐ[ℝ] Module.End ℝ V) (σ : UqSL2 q →ₐ[ℝ] Module.End ℝ W)
    (hρ : IsCompactQuantumPair q (finiteWeightedBilin w b.equivFun.toLinearMap) ρ)
    (hσ : IsCompactQuantumPair q (finiteWeightedBilin z c.equivFun.toLinearMap) σ) :
    IsCompactQuantumPair q (tensorWeightedBilin b c w z) (tensorRepresentation q hq ρ σ) := by
  have hidV := PairAdjoint.id (finiteWeightedBilin w b.equivFun.toLinearMap)
  have hidW := PairAdjoint.id (finiteWeightedBilin z c.equivFun.toLinearMap)
  have hρinv : ρ (uqGenerator q 2)*ρ (uqGenerator q 3)=1 := by rw [← map_mul,uq_inverse,map_one]
  have hσinv : σ (uqGenerator q 2)*σ (uqGenerator q 3)=1 := by rw [← map_mul,uq_inverse,map_one]
  have ht A A' D D' := tensorWeightedBilin_adjoint_map b c w z A A' D D'
  constructor
  · rw [tensorRepresentation_E_end,tensorRepresentation_K_end,tensorRepresentation_F_end,
      mul_add,← TensorProduct.map_mul,← TensorProduct.map_mul,hρinv,mul_one]
    exact (ht _ _ _ _ hρ.adjE hσ.adjK).add (ht _ _ _ _ hidV hσ.adjE)
  · rw [tensorRepresentation_F_end,tensorRepresentation_E_end,tensorRepresentation_Ki_end,
      add_mul,← TensorProduct.map_mul,← TensorProduct.map_mul,hσinv,one_mul]
    exact (ht _ _ _ _ hρ.adjF hidW).add (ht _ _ _ _ hρ.adjKi hσ.adjF)
  · rw [tensorRepresentation_K_end]
    exact ht _ _ _ _ hρ.adjK hσ.adjK
  · rw [tensorRepresentation_Ki_end]
    exact ht _ _ _ _ hρ.adjKi hσ.adjKi

end AMSPhysical

#print axioms AMSPhysical.compactQuantumPair_tensor
