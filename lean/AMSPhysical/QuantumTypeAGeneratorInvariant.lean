import BilinearCyclic
import QuantumTypeAWeights
import PreservingEndAlgebra

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
variable {V I : Type*} [AddCommGroup V] [Module ℝ V]

theorem span_preserving_of_family (f : I → V) (T : Module.End ℝ V)
    (h : ∀ i,T (f i)∈Submodule.span ℝ (Set.range f)) :
    T∈preservingEndAlgebra (Submodule.span ℝ (Set.range f)) := by
  have hle : Submodule.span ℝ (Set.range f)≤(Submodule.span ℝ (Set.range f)).comap T := by
    apply Submodule.span_le.mpr
    rintro x ⟨i,rfl⟩
    exact h i
  exact hle

theorem typeAInvariant_of_generators (q : ℝ) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (S : Submodule ℝ V)
    (h : ∀ (i : Fin n) (t : Fin 4),ρ (typeAAlgebraGenerator q n i t)∈preservingEndAlgebra S) :
    algebraInvariant ρ S := by
  intro z
  obtain ⟨a,rfl⟩ := RingQuot.mkAlgHom_surjective ℝ (QuantumTypeARelation q n) z
  have hm : ρ (RingQuot.mkAlgHom ℝ (QuantumTypeARelation q n) a)∈preservingEndAlgebra S := by
    induction a using FreeAlgebra.induction with
    | grade0 c => simpa only [AlgHom.commutes] using (preservingEndAlgebra S).algebraMap_mem c
    | grade1 it => exact h it.1 it.2
    | mul a b ha hb => simpa only [map_mul] using (preservingEndAlgebra S).mul_mem ha hb
    | add a b ha hb => simpa only [map_add] using (preservingEndAlgebra S).add_mem ha hb
  exact hm

end AMSPhysical
#print axioms AMSPhysical.typeAInvariant_of_generators
