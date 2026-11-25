import QuantumTypeACounit

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Checking an invariant functional on the displayed generators proves its
invariance under every element of the independently presented algebra. -/
theorem typeA_invariantFunctional_of_generators (q : K) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[K] Module.End K V) (f : V →ₗ[K] K)
    (h : ∀ (i : Fin n) (t : Fin 4) v,f (ρ (typeAAlgebraGenerator q n i t) v)=
      typeAQuantumCounit q n (typeAAlgebraGenerator q n i t)*f v) :
    ∀ z : UqTypeA q n,∀ v,f (ρ z v)=typeAQuantumCounit q n z*f v := by
  intro z
  obtain ⟨a,rfl⟩ := RingQuot.mkAlgHom_surjective K (QuantumTypeARelation q n) z
  induction a using FreeAlgebra.induction with
  | grade0 c =>
    intro v
    simp [Algebra.algebraMap_eq_smul_one]
  | grade1 it => exact h it.1 it.2
  | mul a b ha hb =>
    intro v
    simp only [map_mul,Module.End.mul_apply]
    rw [ha,hb]
    ring
  | add a b ha hb =>
    intro v
    simp only [map_add,LinearMap.add_apply]
    rw [ha,hb]
    ring

end AMSPhysical
#print axioms AMSPhysical.typeA_invariantFunctional_of_generators
