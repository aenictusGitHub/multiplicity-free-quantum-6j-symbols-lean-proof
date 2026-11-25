import QuantumTypeAIntertwiner
import QuantumTypeATensorRepresentation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {V W V' W' : Type*}
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup V'] [Module ℝ V'] [AddCommGroup W'] [Module ℝ W']

theorem typeATensorRepresentation_Ki (q : ℝ) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (i : Fin n) (v : V) (w : W) :
    typeATensorRepresentation q hq n ρ σ (typeAAlgebraGenerator q n i 3) (v ⊗ₜ[ℝ] w)=
      ρ (typeAAlgebraGenerator q n i 3) v ⊗ₜ[ℝ] σ (typeAAlgebraGenerator q n i 3) w := by
  simp [typeATensorRepresentation,typeAQuantumCoproduct_generator,typeACoproductKi,
    Module.endTensorEndAlgHom_apply,TensorProduct.AlgebraTensorModule.map_tmul]

theorem typeA_intertwiner_tensor (q : ℝ) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (ρ' : UqTypeA q n →ₐ[ℝ] Module.End ℝ V') (σ' : UqTypeA q n →ₐ[ℝ] Module.End ℝ W')
    (T : V →ₗ[ℝ] V') (S : W →ₗ[ℝ] W')
    (hT : ∀ z v,T (ρ z v)=ρ' z (T v)) (hS : ∀ z w,S (σ z w)=σ' z (S w))
    (z : UqTypeA q n) (v : V ⊗[ℝ] W) :
    TensorProduct.map T S (typeATensorRepresentation q hq n ρ σ z v)=
      typeATensorRepresentation q hq n ρ' σ' z (TensorProduct.map T S v) := by
  apply typeA_intertwiner_of_generators (V:=V ⊗[ℝ] W) (W:=V' ⊗[ℝ] W') q n _ _ _ _ z v
  intro i t x
  have he : (TensorProduct.map T S).comp
        (typeATensorRepresentation q hq n ρ σ (typeAAlgebraGenerator q n i t))=
      (typeATensorRepresentation q hq n ρ' σ' (typeAAlgebraGenerator q n i t)).comp (TensorProduct.map T S) := by
    apply TensorProduct.ext'
    intro p w
    simp only [LinearMap.comp_apply,TensorProduct.map_tmul]
    fin_cases t <;>
      simp [typeATensorRepresentation,typeAQuantumCoproduct_generator,typeACoproductE,
        typeACoproductF,typeACoproductK,typeACoproductKi,Module.endTensorEndAlgHom_apply,
        TensorProduct.AlgebraTensorModule.map_tmul,hT,hS]
  exact DFunLike.congr_fun he x

end AMSPhysical
#print axioms AMSPhysical.typeA_intertwiner_tensor
