import QuantumTypeAAssociator

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {V W U : Type*}
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W] [AddCommGroup U] [Module ℝ U]

theorem typeA_associator_inverse_intertwines (q : ℝ) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (τ : UqTypeA q n →ₐ[ℝ] Module.End ℝ U) (z : UqTypeA q n) (v : V ⊗[ℝ] (W ⊗[ℝ] U)) :
    (TensorProduct.assoc ℝ V W U).symm
      (typeATensorRepresentation q hq n ρ (typeATensorRepresentation q hq n σ τ) z v)=
    typeATensorRepresentation q hq n (typeATensorRepresentation q hq n ρ σ) τ z
      ((TensorProduct.assoc ℝ V W U).symm v) := by
  apply (TensorProduct.assoc ℝ V W U).injective
  rw [LinearEquiv.apply_symm_apply,typeA_associator_intertwines,LinearEquiv.apply_symm_apply]

end AMSPhysical
