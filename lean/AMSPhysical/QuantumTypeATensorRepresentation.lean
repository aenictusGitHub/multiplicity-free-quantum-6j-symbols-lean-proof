import QuantumTypeACoproduct
import QuantumTypeAFinite

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

variable {K : Type*} [Field K]

def typeATensorRepresentation {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (q : K) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[K] Module.End K V) (σ : UqTypeA q n →ₐ[K] Module.End K W) :
    UqTypeA q n →ₐ[K] Module.End K (V ⊗[K] W) :=
  (Module.endTensorEndAlgHom (R:=K) (S:=K) (A:=K) (M:=V) (N:=W)).comp
    ((Algebra.TensorProduct.map ρ σ).comp (typeAQuantumCoproduct q hq n))

theorem typeATensorRepresentation_E {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (q : K) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[K] Module.End K V) (σ : UqTypeA q n →ₐ[K] Module.End K W) (i : Fin n) (v : V) (w : W) :
    typeATensorRepresentation q hq n ρ σ (typeAAlgebraGenerator q n i 0) (v ⊗ₜ[K] w)=
      (ρ (typeAAlgebraGenerator q n i 0) v) ⊗ₜ[K] (σ (typeAAlgebraGenerator q n i 2) w)+
        v ⊗ₜ[K] (σ (typeAAlgebraGenerator q n i 0) w) := by
  simp [typeATensorRepresentation,typeAQuantumCoproduct_generator,typeACoproductE,
    Module.endTensorEndAlgHom_apply,TensorProduct.AlgebraTensorModule.map_tmul]

theorem typeATensorRepresentation_F {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (q : K) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[K] Module.End K V) (σ : UqTypeA q n →ₐ[K] Module.End K W) (i : Fin n) (v : V) (w : W) :
    typeATensorRepresentation q hq n ρ σ (typeAAlgebraGenerator q n i 1) (v ⊗ₜ[K] w)=
      (ρ (typeAAlgebraGenerator q n i 1) v) ⊗ₜ[K] w+
        (ρ (typeAAlgebraGenerator q n i 3) v) ⊗ₜ[K] (σ (typeAAlgebraGenerator q n i 1) w) := by
  simp [typeATensorRepresentation,typeAQuantumCoproduct_generator,typeACoproductF,
    Module.endTensorEndAlgHom_apply,TensorProduct.AlgebraTensorModule.map_tmul]

theorem typeATensorRepresentation_K {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (q : K) (hq : q≠0) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[K] Module.End K V) (σ : UqTypeA q n →ₐ[K] Module.End K W) (i : Fin n) (v : V) (w : W) :
    typeATensorRepresentation q hq n ρ σ (typeAAlgebraGenerator q n i 2) (v ⊗ₜ[K] w)=
      (ρ (typeAAlgebraGenerator q n i 2) v) ⊗ₜ[K] (σ (typeAAlgebraGenerator q n i 2) w) := by
  simp [typeATensorRepresentation,typeAQuantumCoproduct_generator,typeACoproductK,
    Module.endTensorEndAlgHom_apply,TensorProduct.AlgebraTensorModule.map_tmul]

/-- Tensor product of the independently constructed finite-dimensional quantum modules. -/
def finiteTypeATensorRepresentation (q : K) (hq : q≠0) (n : ℕ) (hden : q-q⁻¹≠0) (l m : ℕ) :
    UqTypeA q n →ₐ[K] Module.End K (quantumOccupationSpace K (Fin (n+1)) l ⊗[K] quantumOccupationSpace K (Fin (n+1)) m) :=
  typeATensorRepresentation q hq n (typeAFiniteQuantumRepresentation q hq hden n l)
    (typeAFiniteQuantumRepresentation q hq hden n m)

end AMSPhysical

#print axioms AMSPhysical.finiteTypeATensorRepresentation
