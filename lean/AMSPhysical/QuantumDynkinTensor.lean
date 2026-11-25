import QuantumDynkinCoproduct
import QuantumTypeATensorRepresentation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

theorem typeATensorRepresentation_dynkin (q : ℝ) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (z : UqTypeA q n) (v : V ⊗[ℝ] W) :
    typeATensorRepresentation q hq n (ρ.comp (typeADynkinReflection q n))
        (σ.comp (typeADynkinReflection q n)) z v=
      typeATensorRepresentation q hq n ρ σ (typeADynkinReflection q n z) v := by
  have h := congrArg (fun f =>f z) (typeADynkinReflection_coproduct q hq n)
  change Algebra.TensorProduct.map (typeADynkinReflection q n) (typeADynkinReflection q n)
    (typeAQuantumCoproduct q hq n z)=typeAQuantumCoproduct q hq n (typeADynkinReflection q n z) at h
  unfold typeATensorRepresentation
  simp only [AlgHom.comp_apply,Algebra.TensorProduct.map_comp]
  rw [h]

end AMSPhysical
