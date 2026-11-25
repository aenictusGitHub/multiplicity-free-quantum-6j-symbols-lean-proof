import HighestLineEmbedding

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  {q : ℝ} {n : ℕ}

theorem intertwiner_highest_mem {lam : Fin n → ℤ}
    (X : CompactHighestRealization q n V lam) (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (F : V →ₗ[ℝ] W) (hF : ∀ z v,F (X.action z v)=ρ z (F v)) :
    F X.highest∈typeAHighestSpace q n ρ lam := by
  apply (mem_typeAHighestSpace q n ρ lam _).mpr
  constructor
  · intro i;rw [← hF,X.highestE,map_zero]
  · intro i;rw [← hF,X.highestK,map_smul]

def highestSpaceMap (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V)
    (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W) (lam : Fin n → ℤ) (E : V →ₗ[ℝ] W)
    (hE : ∀ z v,E (ρ z v)=σ z (E v)) : typeAHighestSpace q n ρ lam →ₗ[ℝ] typeAHighestSpace q n σ lam :=
  (E.comp (typeAHighestSpace q n ρ lam).subtype).codRestrict _ (by
    intro v
    obtain ⟨hRaise,hCartan⟩:=(mem_typeAHighestSpace q n ρ lam v.val).mp v.property
    apply (mem_typeAHighestSpace q n σ lam _).mpr
    constructor
    · intro i;change σ _ (E v.val)=0;rw [← hE,hRaise,map_zero]
    · intro i;change σ _ (E v.val)=q^(lam i) • E v.val;rw [← hE,hCartan,map_smul])

theorem highestSpaceMap_injective (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V)
    (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W) (lam : Fin n → ℤ) (E : V →ₗ[ℝ] W)
    (hE : ∀ z v,E (ρ z v)=σ z (E v)) (hInj : Function.Injective E) :
    Function.Injective (highestSpaceMap ρ σ lam E hE) := by
  intro v w he
  exact Subtype.ext (hInj (congrArg Subtype.val he))

end AMSPhysical
#print axioms AMSPhysical.highestSpaceMap_injective
