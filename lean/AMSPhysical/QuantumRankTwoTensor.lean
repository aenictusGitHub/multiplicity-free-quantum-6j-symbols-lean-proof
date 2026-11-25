import QuantumRankTwoCoproduct
import QuantumTypeATensorIntertwiner
import QuantumTensorRepresentation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

theorem rankTwo_tensor_pullback (q : ℝ) (hq : q≠0)
    (ρ : UqSL2 q →ₐ[ℝ] Module.End ℝ V) (σ : UqSL2 q →ₐ[ℝ] Module.End ℝ W) :
    typeATensorRepresentation q hq 1 (ρ.comp (rankTwoToSL2 q)) (σ.comp (rankTwoToSL2 q))=
      (tensorRepresentation q hq ρ σ).comp (rankTwoToSL2 q) := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext it
  obtain ⟨i,t⟩:=it
  change typeATensorRepresentation q hq 1 (ρ.comp (rankTwoToSL2 q)) (σ.comp (rankTwoToSL2 q))
    (typeAAlgebraGenerator q 1 i t)=tensorRepresentation q hq ρ σ (rankTwoToSL2 q (typeAAlgebraGenerator q 1 i t))
  rw [rankTwoToSL2_generator]
  apply TensorProduct.ext'
  intro v w
  fin_cases t <;>
    simp [typeATensorRepresentation,tensorRepresentation,typeAQuantumCoproduct_generator,
      quantumCoproduct_generator,typeACoproductE,typeACoproductF,typeACoproductK,typeACoproductKi,
      coproductE,coproductF,coproductK,coproductKinv,rankTwoToSL2_generator,
      Module.endTensorEndAlgHom_apply,TensorProduct.AlgebraTensorModule.map_tmul]

end AMSPhysical
#print axioms AMSPhysical.rankTwo_tensor_pullback
