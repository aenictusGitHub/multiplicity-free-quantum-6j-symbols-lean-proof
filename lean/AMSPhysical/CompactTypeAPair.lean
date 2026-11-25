import QuantumTypeATensorRepresentation
import QuantumTypeARelations
import BilinearAdjoint

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

structure IsCompactTypeAPair (q : ℝ) (n : ℕ) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) : Prop where
  adjE : ∀ i : Fin n,PairAdjoint B (ρ (typeAAlgebraGenerator q n i 0))
    (ρ (typeAAlgebraGenerator q n i 2)*ρ (typeAAlgebraGenerator q n i 1))
  adjF : ∀ i : Fin n,PairAdjoint B (ρ (typeAAlgebraGenerator q n i 1))
    (ρ (typeAAlgebraGenerator q n i 0)*ρ (typeAAlgebraGenerator q n i 3))
  adjK : ∀ i : Fin n,PairAdjoint B (ρ (typeAAlgebraGenerator q n i 2)) (ρ (typeAAlgebraGenerator q n i 2))
  adjKi : ∀ i : Fin n,PairAdjoint B (ρ (typeAAlgebraGenerator q n i 3)) (ρ (typeAAlgebraGenerator q n i 3))

/-- Every actual algebra element has an adjoint represented by an actual
algebra element. This is proved from the complete generator presentation. -/
theorem IsCompactTypeAPair.adjoint_exists {q : ℝ} {n : ℕ}
    {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V}
    (h : IsCompactTypeAPair q n B ρ) (z : UqTypeA q n) :
    ∃ u : UqTypeA q n,PairAdjoint B (ρ z) (ρ u) := by
  obtain ⟨a,rfl⟩ := RingQuot.mkAlgHom_surjective ℝ (QuantumTypeARelation q n) z
  induction a using FreeAlgebra.induction with
  | grade0 c =>
    refine ⟨algebraMap ℝ (UqTypeA q n) c,?_⟩
    simpa [Algebra.algebraMap_eq_smul_one] using (PairAdjoint.id B).smul c
  | grade1 it =>
    obtain ⟨i,t⟩ := it
    change ∃ u,PairAdjoint B (ρ (typeAAlgebraGenerator q n i t)) (ρ u)
    fin_cases t
    · exact ⟨typeAAlgebraGenerator q n i 2*typeAAlgebraGenerator q n i 1,by simpa only [map_mul] using h.adjE i⟩
    · exact ⟨typeAAlgebraGenerator q n i 0*typeAAlgebraGenerator q n i 3,by simpa only [map_mul] using h.adjF i⟩
    · exact ⟨typeAAlgebraGenerator q n i 2,h.adjK i⟩
    · exact ⟨typeAAlgebraGenerator q n i 3,h.adjKi i⟩
  | mul a b ha hb =>
    obtain ⟨u,hu⟩ := ha
    obtain ⟨v,hv⟩ := hb
    exact ⟨v*u,by simpa only [map_mul] using hu.mul hv⟩
  | add a b ha hb =>
    obtain ⟨u,hu⟩ := ha
    obtain ⟨v,hv⟩ := hb
    exact ⟨u+v,by simpa only [map_add] using hu.add hv⟩

end AMSPhysical
#print axioms AMSPhysical.IsCompactTypeAPair.adjoint_exists
