import QuantumTypeATensorIntertwiner
import QuantumAssociatorIntertwiner

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {V W U : Type*}
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W] [AddCommGroup U] [Module ℝ U]

/-- The literal vector-space associator intertwines the actual general-rank
iterated tensor actions. It is not an assumed recoupling identity. -/
theorem typeA_associator_intertwines (q : ℝ) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (τ : UqTypeA q n →ₐ[ℝ] Module.End ℝ U) (z : UqTypeA q n) (p : (V ⊗[ℝ] W) ⊗[ℝ] U) :
    (TensorProduct.assoc ℝ V W U)
      (typeATensorRepresentation q hq n (typeATensorRepresentation q hq n ρ σ) τ z p)=
    typeATensorRepresentation q hq n ρ (typeATensorRepresentation q hq n σ τ) z
      ((TensorProduct.assoc ℝ V W U) p) := by
  apply typeA_intertwiner_of_generators (V:=(V ⊗[ℝ] W) ⊗[ℝ] U) (W:=V ⊗[ℝ] (W ⊗[ℝ] U))
    q n _ _ (TensorProduct.assoc ℝ V W U).toLinearMap _ z p
  intro i t x
  have he : (TensorProduct.assoc ℝ V W U).toLinearMap.comp
        (typeATensorRepresentation q hq n (typeATensorRepresentation q hq n ρ σ) τ (typeAAlgebraGenerator q n i t))=
      (typeATensorRepresentation q hq n ρ (typeATensorRepresentation q hq n σ τ) (typeAAlgebraGenerator q n i t)).comp
        (TensorProduct.assoc ℝ V W U).toLinearMap := by
    apply tensorTriple_ext (V:=V) (W:=W) (U:=U)
    intro v w u
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
    fin_cases t <;>
      simp [typeATensorRepresentation,typeAQuantumCoproduct_generator,typeACoproductE,
        typeACoproductF,typeACoproductK,typeACoproductKi,Module.endTensorEndAlgHom_apply,
        TensorProduct.AlgebraTensorModule.map_tmul,TensorProduct.assoc_tmul,
        TensorProduct.add_tmul,TensorProduct.tmul_add,add_assoc,Algebra.TensorProduct.one_def]
  exact DFunLike.congr_fun he x

end AMSPhysical
#print axioms AMSPhysical.typeA_associator_intertwines
