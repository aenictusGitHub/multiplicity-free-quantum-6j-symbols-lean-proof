import QuantumTypeAHighestSpace

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

theorem typeAHighestSpace_equiv_mem (q : ℝ) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (e : V ≃ₗ[ℝ] W) (he : ∀ z v,e (ρ z v)=σ z (e v)) (lam : Fin n → ℤ) (v : V) :
    e v∈typeAHighestSpace q n σ lam ↔ v∈typeAHighestSpace q n ρ lam := by
  rw [mem_typeAHighestSpace,mem_typeAHighestSpace]
  constructor
  · rintro ⟨hE,hK⟩
    constructor
    · intro i
      apply e.injective
      rw [he,hE,map_zero]
    · intro i
      apply e.injective
      rw [he,hK,map_smul]
  · rintro ⟨hE,hK⟩
    constructor
    · intro i
      rw [← he,hE,map_zero]
    · intro i
      rw [← he,hK,map_smul]

def typeAHighestSpaceEquiv (q : ℝ) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (e : V ≃ₗ[ℝ] W) (he : ∀ z v,e (ρ z v)=σ z (e v)) (lam : Fin n → ℤ) :
    typeAHighestSpace q n ρ lam ≃ₗ[ℝ] typeAHighestSpace q n σ lam :=
  e.ofSubmodules _ _ (by
    ext w
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact (typeAHighestSpace_equiv_mem q n ρ σ e he lam v).mpr hv
    · intro hw
      exact ⟨e.symm w,(typeAHighestSpace_equiv_mem q n ρ σ e he lam (e.symm w)).mp
        (by rwa [LinearEquiv.apply_symm_apply]),e.apply_symm_apply w⟩)

end AMSPhysical
#print axioms AMSPhysical.typeAHighestSpaceEquiv
