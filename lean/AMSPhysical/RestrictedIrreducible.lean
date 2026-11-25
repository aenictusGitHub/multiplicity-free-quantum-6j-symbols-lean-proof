import InvariantRepresentationRestriction

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical
variable {A V : Type*} [Ring A] [Algebra ℝ A] [AddCommGroup V] [Module ℝ V]

theorem restriction_irreducible (ρ : A →ₐ[ℝ] Module.End ℝ V)
    (C : Submodule ℝ V) (hC : algebraInvariant ρ C)
    (hI : ∀ S : Submodule ℝ V,S≤C → algebraInvariant ρ S → S=⊥ ∨ S=C)
    (S : Submodule ℝ C) (hS : algebraInvariant (invariantRepresentationRestriction ρ C hC) S) :
    S=⊥ ∨ S=⊤ := by
  let T := S.map C.subtype
  have hTC : T≤C := by
    rintro x ⟨u,hu,rfl⟩
    exact u.property
  have hT : algebraInvariant ρ T := by
    rintro z x ⟨u,hu,rfl⟩
    refine ⟨invariantRepresentationRestriction ρ C hC z u,hS z u hu,?_⟩
    rfl
  rcases hI T hTC hT with hz | ht
  · left
    apply le_antisymm _ bot_le
    intro x hx
    have hm : x.val∈T := ⟨x,hx,rfl⟩
    rw [hz,Submodule.mem_bot] at hm
    change x=0
    exact Subtype.ext hm
  · right
    apply le_antisymm le_top
    intro x hx
    have hm : x.val∈T := by rw [ht];exact x.property
    obtain ⟨u,hu,he⟩ := hm
    have hux : u=x := Subtype.ext he
    simpa only [hux] using hu

end AMSPhysical
#print axioms AMSPhysical.restriction_irreducible
