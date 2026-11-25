import QuantumPhysicalCupHighest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def typeAHighestSpace (q : ℝ) (n : ℕ) (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (lam : Fin n → ℤ) : Submodule ℝ V :=
  (⨅ i : Fin n,LinearMap.ker (ρ (typeAAlgebraGenerator q n i 0))) ⊓
    (⨅ i : Fin n,LinearMap.ker (ρ (typeAAlgebraGenerator q n i 2)-q^(lam i) • LinearMap.id))

theorem mem_typeAHighestSpace (q : ℝ) (n : ℕ) (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (lam : Fin n → ℤ) (v : V) :
    v∈typeAHighestSpace q n ρ lam ↔
      (∀ i : Fin n,ρ (typeAAlgebraGenerator q n i 0) v=0) ∧
        (∀ i : Fin n,ρ (typeAAlgebraGenerator q n i 2) v=q^(lam i) • v) := by
  simp only [typeAHighestSpace,Submodule.mem_inf,Submodule.mem_iInf,LinearMap.mem_ker,
    LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply,sub_eq_zero]

theorem physicalQuantumCupSpan_le_highest (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n l m h c : ℕ) :
    physicalQuantumCupSpan q n l m h c ≤ typeAHighestSpace (V:=quantumOccupationTripleSpace n l (m+h) c) q n (typeAMixedTriple q hq hD n l (m+h) c)
      (mixedHighestDynkin n (l+c-m) h) := by
  apply Submodule.span_le.mpr
  rintro v ⟨r,rfl⟩
  apply (mem_typeAHighestSpace q n _ _ _).mpr
  exact ⟨physicalQuantumCupVector_E q hq hD n l m h c r,physicalQuantumCupVector_K q hq hD n l m h c r⟩

end AMSPhysical
