import QuantumTypeAAssociatorInverse

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {V W U V' W' U' : Type*}
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W] [AddCommGroup U] [Module ℝ U]
  [AddCommGroup V'] [Module ℝ V'] [AddCommGroup W'] [Module ℝ W'] [AddCommGroup U'] [Module ℝ U']

theorem typeA_associatedTensorIntertwiner (q : ℝ) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (τ : UqTypeA q n →ₐ[ℝ] Module.End ℝ U)
    (ρ' : UqTypeA q n →ₐ[ℝ] Module.End ℝ V') (σ' : UqTypeA q n →ₐ[ℝ] Module.End ℝ W')
    (τ' : UqTypeA q n →ₐ[ℝ] Module.End ℝ U')
    (T : (V ⊗[ℝ] W) →ₗ[ℝ] V' ⊗[ℝ] W') (S : U →ₗ[ℝ] U')
    (hT : ∀ z v,T (typeATensorRepresentation q hq n ρ σ z v)=typeATensorRepresentation q hq n ρ' σ' z (T v))
    (hS : ∀ z v,S (τ z v)=τ' z (S v)) (z : UqTypeA q n) (v : V ⊗[ℝ] (W ⊗[ℝ] U)) :
    (TensorProduct.assoc ℝ V' W' U')
      (TensorProduct.map T S ((TensorProduct.assoc ℝ V W U).symm
        (typeATensorRepresentation q hq n ρ (typeATensorRepresentation q hq n σ τ) z v)))=
      typeATensorRepresentation q hq n ρ' (typeATensorRepresentation q hq n σ' τ') z
        ((TensorProduct.assoc ℝ V' W' U') (TensorProduct.map T S ((TensorProduct.assoc ℝ V W U).symm v))) := by
  rw [typeA_associator_inverse_intertwines,typeA_intertwiner_tensor q hq n _ _ _ _ T S hT hS,
    typeA_associator_intertwines]

end AMSPhysical
