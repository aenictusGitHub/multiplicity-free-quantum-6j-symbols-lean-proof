import QuantumTypeABending

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {X V W U : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [AddCommGroup U] [Module ℝ U]

theorem bendRight_comp (T : X ⊗[ℝ] V →ₗ[ℝ] W) (J : W →ₗ[ℝ] U) (cup : V ⊗[ℝ] V) :
    bendRight (J.comp T) cup=(TensorProduct.map J (LinearMap.id : Module.End ℝ V)).comp (bendRight T cup) := by
  unfold bendRight
  have he : TensorProduct.map (J.comp T) (LinearMap.id : Module.End ℝ V)=
      (TensorProduct.map J (LinearMap.id : Module.End ℝ V)).comp
        (TensorProduct.map T (LinearMap.id : Module.End ℝ V)) := by
    apply TensorProduct.ext'
    intro x v
    simp only [TensorProduct.map_tmul,LinearMap.comp_apply,LinearMap.id_apply]
  rw [he]
  simp only [LinearMap.comp_assoc]

/-- Bending preserves the actual target channel factorization. -/
theorem bendRight_mem_tensor_range (S : Submodule ℝ W) (T : X ⊗[ℝ] V →ₗ[ℝ] W)
    (hT : ∀ v,T v∈S) (cup : V ⊗[ℝ] V) (x : X) :
    bendRight T cup x∈LinearMap.range (TensorProduct.map S.subtype (LinearMap.id : Module.End ℝ V)) := by
  let T' : X ⊗[ℝ] V →ₗ[ℝ] S:=T.codRestrict S hT
  have he : T=S.subtype.comp T' := rfl
  rw [he,bendRight_comp]
  exact ⟨bendRight T' cup x,rfl⟩

end AMSPhysical
#print axioms AMSPhysical.bendRight_mem_tensor_range
