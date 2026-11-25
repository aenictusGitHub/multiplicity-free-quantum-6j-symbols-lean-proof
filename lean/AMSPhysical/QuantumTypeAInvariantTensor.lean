import QuantumTypeATensorIntertwiner
import QuantumTypeACounit

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

def tensorWithRightVector (w : W) : V →ₗ[ℝ] V ⊗[ℝ] W := (TensorProduct.mk ℝ V W).flip w
def tensorWithLeftVector (v : V) : W →ₗ[ℝ] V ⊗[ℝ] W := TensorProduct.mk ℝ V W v

theorem typeA_tensor_invariant_right (q : ℝ) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (w : W) (hw : ∀ z,σ z w=typeAQuantumCounit q n z • w) (z : UqTypeA q n) (v : V) :
    tensorWithRightVector w (ρ z v)=typeATensorRepresentation q hq n ρ σ z (tensorWithRightVector w v) := by
  apply typeA_intertwiner_of_generators q n ρ (typeATensorRepresentation q hq n ρ σ) (tensorWithRightVector w) _ z v
  intro i t x
  change ρ (typeAAlgebraGenerator q n i t) x ⊗ₜ[ℝ] w=
    typeATensorRepresentation q hq n ρ σ (typeAAlgebraGenerator q n i t) (x ⊗ₜ[ℝ] w)
  fin_cases t <;>
    simp [typeATensorRepresentation,typeAQuantumCoproduct_generator,typeACoproductE,typeACoproductF,
      typeACoproductK,typeACoproductKi,Module.endTensorEndAlgHom_apply,
      TensorProduct.AlgebraTensorModule.map_tmul,hw,typeAQuantumCounit_generator]

theorem typeA_tensor_invariant_left (q : ℝ) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (v : V) (hv : ∀ z,ρ z v=typeAQuantumCounit q n z • v) (z : UqTypeA q n) (w : W) :
    tensorWithLeftVector v (σ z w)=typeATensorRepresentation q hq n ρ σ z (tensorWithLeftVector v w) := by
  apply typeA_intertwiner_of_generators q n σ (typeATensorRepresentation q hq n ρ σ) (tensorWithLeftVector v) _ z w
  intro i t x
  change v ⊗ₜ[ℝ] σ (typeAAlgebraGenerator q n i t) x=
    typeATensorRepresentation q hq n ρ σ (typeAAlgebraGenerator q n i t) (v ⊗ₜ[ℝ] x)
  fin_cases t <;>
    simp [typeATensorRepresentation,typeAQuantumCoproduct_generator,typeACoproductE,typeACoproductF,
      typeACoproductK,typeACoproductKi,Module.endTensorEndAlgHom_apply,
      TensorProduct.AlgebraTensorModule.map_tmul,hv,typeAQuantumCounit_generator]

end AMSPhysical
