import QuantumTypeAInvariantTensor
import QuantumTypeAAssociatorInverse

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {V W D B : Type*}
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup D] [Module ℝ D] [AddCommGroup B] [Module ℝ B]

def bendRight (T : (V ⊗[ℝ] D) →ₗ[ℝ] W) (cup : D ⊗[ℝ] B) : V →ₗ[ℝ] W ⊗[ℝ] B :=
  (TensorProduct.map T (LinearMap.id : B →ₗ[ℝ] B)).comp
    ((TensorProduct.assoc ℝ V D B).symm.toLinearMap.comp (tensorWithRightVector cup))

/-- Actual tensor-duality bending preserves full-algebra intertwining.
The cup is independently supplied with its proved counit invariance. -/
theorem typeA_bendRight_intertwines (q : ℝ) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (τ : UqTypeA q n →ₐ[ℝ] Module.End ℝ D) (κ : UqTypeA q n →ₐ[ℝ] Module.End ℝ B)
    (T : (V ⊗[ℝ] D) →ₗ[ℝ] W) (cup : D ⊗[ℝ] B)
    (hT : ∀ z v,T (typeATensorRepresentation q hq n ρ τ z v)=σ z (T v))
    (hCup : ∀ z,typeATensorRepresentation q hq n τ κ z cup=typeAQuantumCounit q n z • cup)
    (z : UqTypeA q n) (v : V) :
    bendRight T cup (ρ z v)=typeATensorRepresentation q hq n σ κ z (bendRight T cup v) := by
  unfold bendRight
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [typeA_tensor_invariant_right q hq n ρ (typeATensorRepresentation q hq n τ κ) cup hCup,
    typeA_associator_inverse_intertwines]
  exact typeA_intertwiner_tensor q hq n (typeATensorRepresentation q hq n ρ τ) κ σ κ T LinearMap.id hT
    (fun _ _ =>rfl) z _

end AMSPhysical
#print axioms AMSPhysical.typeA_bendRight_intertwines
