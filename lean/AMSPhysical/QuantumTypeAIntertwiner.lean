import QuantumTypeAFunctional

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Intertwining the presented generators suffices for the actual quotient
algebra; no additional presentation relation is assumed here. -/
theorem typeA_intertwiner_of_generators (q : K) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[K] Module.End K V) (σ : UqTypeA q n →ₐ[K] Module.End K W)
    (T : V →ₗ[K] W)
    (h : ∀ i : Fin n,∀ t : Fin 4,∀ v : V,T (ρ (typeAAlgebraGenerator q n i t) v)=
      σ (typeAAlgebraGenerator q n i t) (T v)) (z : UqTypeA q n) (v : V) :
    T (ρ z v)=σ z (T v) := by
  obtain ⟨a,rfl⟩ := RingQuot.mkAlgHom_surjective K (QuantumTypeARelation q n) z
  revert v
  induction a using FreeAlgebra.induction with
  | grade0 c =>
    intro v
    simp only [AlgHom.commutes,Algebra.algebraMap_eq_smul_one,LinearMap.smul_apply,
      Module.End.one_apply,map_smul,map_one]
  | grade1 it => exact h it.1 it.2
  | mul a b ha hb =>
    intro v
    simp only [map_mul,Module.End.mul_apply,ha,hb]
  | add a b ha hb =>
    intro v
    simp only [map_add,LinearMap.add_apply,ha,hb]

end AMSPhysical
