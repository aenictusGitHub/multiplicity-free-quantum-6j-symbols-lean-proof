import QuantumCoproduct
import FiniteQuantumRepresentation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

variable {K : Type*} [Field K]

def tensorRepresentation {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (q : K) (hq : q≠0)
    (ρ : UqSL2 q →ₐ[K] Module.End K V) (σ : UqSL2 q →ₐ[K] Module.End K W) :
    UqSL2 q →ₐ[K] Module.End K (V ⊗[K] W) :=
  (Module.endTensorEndAlgHom (R:=K) (S:=K) (A:=K) (M:=V) (N:=W)).comp
    ((Algebra.TensorProduct.map ρ σ).comp (quantumCoproduct q hq))

theorem tensorRepresentation_E {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (q : K) (hq : q≠0)
    (ρ : UqSL2 q →ₐ[K] Module.End K V) (σ : UqSL2 q →ₐ[K] Module.End K W) (v : V) (w : W) :
    tensorRepresentation q hq ρ σ (uqGenerator q 0) (v ⊗ₜ[K] w)=
      (ρ (uqGenerator q 0) v) ⊗ₜ[K] (σ (uqGenerator q 2) w)+
        v ⊗ₜ[K] (σ (uqGenerator q 0) w) := by
  simp [tensorRepresentation,quantumCoproduct_generator,coproductE,
    Module.endTensorEndAlgHom_apply,TensorProduct.AlgebraTensorModule.map_tmul]

theorem tensorRepresentation_F {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (q : K) (hq : q≠0)
    (ρ : UqSL2 q →ₐ[K] Module.End K V) (σ : UqSL2 q →ₐ[K] Module.End K W) (v : V) (w : W) :
    tensorRepresentation q hq ρ σ (uqGenerator q 1) (v ⊗ₜ[K] w)=
      (ρ (uqGenerator q 1) v) ⊗ₜ[K] w+
        (ρ (uqGenerator q 3) v) ⊗ₜ[K] (σ (uqGenerator q 1) w) := by
  simp [tensorRepresentation,quantumCoproduct_generator,coproductF,
    Module.endTensorEndAlgHom_apply,TensorProduct.AlgebraTensorModule.map_tmul]

theorem tensorRepresentation_K {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (q : K) (hq : q≠0)
    (ρ : UqSL2 q →ₐ[K] Module.End K V) (σ : UqSL2 q →ₐ[K] Module.End K W) (v : V) (w : W) :
    tensorRepresentation q hq ρ σ (uqGenerator q 2) (v ⊗ₜ[K] w)=
      (ρ (uqGenerator q 2) v) ⊗ₜ[K] (σ (uqGenerator q 2) w) := by
  simp [tensorRepresentation,quantumCoproduct_generator,coproductK,
    Module.endTensorEndAlgHom_apply,TensorProduct.AlgebraTensorModule.map_tmul]

/-- Tensor product of the independently constructed finite-dimensional quantum modules. -/
def finiteTensorRepresentation (q : K) (hq : q≠0) (hden : q-q⁻¹≠0) (l m : ℕ) :
    UqSL2 q →ₐ[K] Module.End K (finiteWeightSpace (K:=K) l ⊗[K] finiteWeightSpace (K:=K) m) :=
  tensorRepresentation q hq (finiteQuantumRepresentation q hq hden l)
    (finiteQuantumRepresentation q hq hden m)

end AMSPhysical

#print axioms AMSPhysical.finiteTensorRepresentation
