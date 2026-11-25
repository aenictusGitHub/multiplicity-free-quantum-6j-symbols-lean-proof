import QuantumTypeAFunctional

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem typeA_invariantVector_of_generators (q : K) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[K] Module.End K V) (v : V)
    (h : ∀ (i : Fin n) (t : Fin 4),ρ (typeAAlgebraGenerator q n i t) v=
      typeAQuantumCounit q n (typeAAlgebraGenerator q n i t) • v) :
    ∀ z : UqTypeA q n,ρ z v=typeAQuantumCounit q n z • v := by
  intro z
  obtain ⟨a,rfl⟩ := RingQuot.mkAlgHom_surjective K (QuantumTypeARelation q n) z
  induction a using FreeAlgebra.induction with
  | grade0 c => simp [Algebra.algebraMap_eq_smul_one]
  | grade1 it => exact h it.1 it.2
  | mul a b ha hb =>
    simp only [map_mul,Module.End.mul_apply]
    rw [hb,map_smul,ha,smul_smul,mul_comm]
  | add a b ha hb =>
    simp only [map_add,LinearMap.add_apply,ha,hb,add_smul]

end AMSPhysical
