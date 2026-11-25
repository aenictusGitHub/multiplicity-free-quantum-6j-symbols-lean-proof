import FiniteRightBending
import QuantumTypeATripleIntertwiner

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {X V W P : Type*}
  [AddCommGroup X] [Module ℝ X] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [AddCommGroup P] [Module ℝ P]

def tensorRightEvaluation (ev : P →ₗ[ℝ] ℝ) : (W ⊗[ℝ] P) →ₗ[ℝ] W :=
  (TensorProduct.rid ℝ W).toLinearMap.comp
    (TensorProduct.map (LinearMap.id : W →ₗ[ℝ] W) ev)

theorem tensorRightEvaluation_tmul (ev : P →ₗ[ℝ] ℝ) (w : W) (p : P) :
    tensorRightEvaluation ev (w ⊗ₜ[ℝ] p)=ev p • w := rfl

theorem typeA_tensorRightEvaluation_intertwines (q : ℝ) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ P)
    (ev : P →ₗ[ℝ] ℝ) (he : ∀ z v,ev (σ z v)=typeAQuantumCounit q n z*ev v)
    (z : UqTypeA q n) (v : W ⊗[ℝ] P) :
    tensorRightEvaluation ev (typeATensorRepresentation q hq n ρ σ z v)=
      ρ z (tensorRightEvaluation ev v) := by
  apply typeA_intertwiner_of_generators q n _ ρ (tensorRightEvaluation ev) _ z v
  intro i t x
  have hh : (tensorRightEvaluation (W:=W) ev).comp
      (typeATensorRepresentation q hq n ρ σ (typeAAlgebraGenerator q n i t))=
      (ρ (typeAAlgebraGenerator q n i t)).comp (tensorRightEvaluation ev) := by
    apply TensorProduct.ext'
    intro w p
    simp only [LinearMap.comp_apply]
    fin_cases t <;>
      simp [typeATensorRepresentation,typeAQuantumCoproduct_generator,typeACoproductE,
        typeACoproductF,typeACoproductK,typeACoproductKi,Module.endTensorEndAlgHom_apply,
        TensorProduct.AlgebraTensorModule.map_tmul,tensorRightEvaluation_tmul,he,
        typeAQuantumCounit_generator]
  exact DFunLike.congr_fun hh x

theorem typeA_unbendRight_intertwines (q : ℝ) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ X) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (τ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (κ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V)
    (S : X →ₗ[ℝ] W ⊗[ℝ] V) (ev : (V ⊗[ℝ] V) →ₗ[ℝ] ℝ)
    (hS : ∀ z v,S (ρ z v)=typeATensorRepresentation q hq n σ τ z (S v))
    (he : ∀ z v,ev (typeATensorRepresentation q hq n τ κ z v)=typeAQuantumCounit q n z*ev v)
    (z : UqTypeA q n) (v : X ⊗[ℝ] V) :
    unbendRight S ev (typeATensorRepresentation q hq n ρ κ z v)=σ z (unbendRight S ev v) := by
  change tensorRightEvaluation ev
      ((TensorProduct.assoc ℝ W V V)
        (TensorProduct.map S (LinearMap.id : V →ₗ[ℝ] V)
          (typeATensorRepresentation q hq n ρ κ z v)))=_
  rw [typeA_intertwiner_tensor q hq n ρ κ (typeATensorRepresentation q hq n σ τ) κ S LinearMap.id
    hS (fun _ _ =>rfl),typeA_associator_intertwines,
    typeA_tensorRightEvaluation_intertwines q hq n σ (typeATensorRepresentation q hq n τ κ) ev he]
  rfl

end AMSPhysical
#print axioms AMSPhysical.typeA_unbendRight_intertwines
