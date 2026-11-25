import QuantumTensorIntertwiner
import Mathlib.LinearAlgebra.TensorProduct.Associator

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct
variable {V W U X : Type*}
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]

theorem tensorTriple_ext (T S : ((V ⊗[ℝ] W) ⊗[ℝ] U) →ₗ[ℝ] X)
    (h : ∀ v w u,T ((v ⊗ₜ[ℝ] w) ⊗ₜ[ℝ] u)=S ((v ⊗ₜ[ℝ] w) ⊗ₜ[ℝ] u)) : T=S := by
  apply TensorProduct.ext'
  intro p u
  induction p using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.zero_tmul,map_zero]
  | tmul v w => exact h v w u
  | add p v hp hv => simp only [TensorProduct.add_tmul,map_add,hp,hv]

theorem tensorRepresentation_Ki (q : ℝ) (hq : q≠0)
    (ρ : UqSL2 q →ₐ[ℝ] Module.End ℝ V) (σ : UqSL2 q →ₐ[ℝ] Module.End ℝ W) (v : V) (w : W) :
    tensorRepresentation q hq ρ σ (uqGenerator q 3) (v ⊗ₜ[ℝ] w)=
      (ρ (uqGenerator q 3) v) ⊗ₜ[ℝ] (σ (uqGenerator q 3) w) := by
  rw [tensorRepresentation_Ki_end,TensorProduct.map_tmul]

/-- The usual vector-space associator intertwines the independently presented iterated coproduct actions. -/
theorem quantumAssociator_intertwines (q : ℝ) (hq : q≠0)
    (ρ : UqSL2 q →ₐ[ℝ] Module.End ℝ V) (σ : UqSL2 q →ₐ[ℝ] Module.End ℝ W)
    (τ : UqSL2 q →ₐ[ℝ] Module.End ℝ U) :
    IsQuantumIntertwiner (V:=(V ⊗[ℝ] W) ⊗[ℝ] U) (W:=V ⊗[ℝ] (W ⊗[ℝ] U)) q
      (tensorRepresentation q hq (tensorRepresentation q hq ρ σ) τ)
      (tensorRepresentation q hq ρ (tensorRepresentation q hq σ τ))
      (TensorProduct.assoc ℝ V W U).toLinearMap := by
  apply quantumIntertwiner_of_generators
  intro i p
  have he : (tensorRepresentation q hq ρ (tensorRepresentation q hq σ τ) (uqGenerator q i)).comp
      (TensorProduct.assoc ℝ V W U).toLinearMap=
      (TensorProduct.assoc ℝ V W U).toLinearMap.comp
        (tensorRepresentation q hq (tensorRepresentation q hq ρ σ) τ (uqGenerator q i)) := by
    apply tensorTriple_ext (V:=V) (W:=W) (U:=U)
    intro v w u
    fin_cases i
    · change tensorRepresentation q hq ρ (tensorRepresentation q hq σ τ) (uqGenerator q 0)
        ((TensorProduct.assoc ℝ V W U) ((v ⊗ₜ[ℝ] w) ⊗ₜ[ℝ] u))=
        (TensorProduct.assoc ℝ V W U)
          (tensorRepresentation q hq (tensorRepresentation q hq ρ σ) τ (uqGenerator q 0) ((v ⊗ₜ[ℝ] w) ⊗ₜ[ℝ] u))
      simp only [TensorProduct.assoc_tmul,
        tensorRepresentation_E (V:=V) (W:=W ⊗[ℝ] U),tensorRepresentation_E (V:=W) (W:=U),
        tensorRepresentation_E (V:=V ⊗[ℝ] W) (W:=U),tensorRepresentation_E (V:=V) (W:=W),
        tensorRepresentation_K (V:=W) (W:=U),map_add,TensorProduct.add_tmul,TensorProduct.tmul_add,
        TensorProduct.assoc_tmul,add_assoc]
    · change tensorRepresentation q hq ρ (tensorRepresentation q hq σ τ) (uqGenerator q 1)
        ((TensorProduct.assoc ℝ V W U) ((v ⊗ₜ[ℝ] w) ⊗ₜ[ℝ] u))=
        (TensorProduct.assoc ℝ V W U)
          (tensorRepresentation q hq (tensorRepresentation q hq ρ σ) τ (uqGenerator q 1) ((v ⊗ₜ[ℝ] w) ⊗ₜ[ℝ] u))
      simp only [TensorProduct.assoc_tmul,
        tensorRepresentation_F (V:=V) (W:=W ⊗[ℝ] U),tensorRepresentation_F (V:=W) (W:=U),
        tensorRepresentation_F (V:=V ⊗[ℝ] W) (W:=U),tensorRepresentation_F (V:=V) (W:=W),
        tensorRepresentation_Ki (V:=V) (W:=W),map_add,TensorProduct.add_tmul,TensorProduct.tmul_add,
        TensorProduct.assoc_tmul,add_assoc]
    · change tensorRepresentation q hq ρ (tensorRepresentation q hq σ τ) (uqGenerator q 2)
        ((TensorProduct.assoc ℝ V W U) ((v ⊗ₜ[ℝ] w) ⊗ₜ[ℝ] u))=
        (TensorProduct.assoc ℝ V W U)
          (tensorRepresentation q hq (tensorRepresentation q hq ρ σ) τ (uqGenerator q 2) ((v ⊗ₜ[ℝ] w) ⊗ₜ[ℝ] u))
      simp only [TensorProduct.assoc_tmul,tensorRepresentation_K (V:=V) (W:=W ⊗[ℝ] U),
        tensorRepresentation_K (V:=W) (W:=U),tensorRepresentation_K (V:=V ⊗[ℝ] W) (W:=U),
        tensorRepresentation_K (V:=V) (W:=W),TensorProduct.assoc_tmul]
    · change tensorRepresentation q hq ρ (tensorRepresentation q hq σ τ) (uqGenerator q 3)
        ((TensorProduct.assoc ℝ V W U) ((v ⊗ₜ[ℝ] w) ⊗ₜ[ℝ] u))=
        (TensorProduct.assoc ℝ V W U)
          (tensorRepresentation q hq (tensorRepresentation q hq ρ σ) τ (uqGenerator q 3) ((v ⊗ₜ[ℝ] w) ⊗ₜ[ℝ] u))
      simp only [TensorProduct.assoc_tmul,tensorRepresentation_Ki (V:=V) (W:=W ⊗[ℝ] U),
        tensorRepresentation_Ki (V:=W) (W:=U),tensorRepresentation_Ki (V:=V ⊗[ℝ] W) (W:=U),
        tensorRepresentation_Ki (V:=V) (W:=W),TensorProduct.assoc_tmul]
  exact DFunLike.congr_fun he p

end AMSPhysical

#print axioms AMSPhysical.quantumAssociator_intertwines
