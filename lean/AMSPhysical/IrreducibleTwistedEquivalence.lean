import CyclicTwistedEquivalence

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {A V W : Type*} [Ring A] [Algebra ℝ A] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

theorem irreducible_map_of_twisted_equivalence (ρ : A →ₐ[ℝ] Module.End ℝ V) (σ : A →ₐ[ℝ] Module.End ℝ W)
    (α : A →ₐ[ℝ] A) (T : V ≃ₗ[ℝ] W) (hT : ∀ z v,T (ρ z v)=σ (α z) (T v))
    (C : Submodule ℝ V)
    (hC : ∀ S : Submodule ℝ V,S≤C → algebraInvariant ρ S → S=⊥ ∨ S=C)
    (S : Submodule ℝ W) (hSC : S≤C.map T.toLinearMap) (hS : algebraInvariant σ S) :
    S=⊥ ∨ S=C.map T.toLinearMap := by
  have hle : S.comap T.toLinearMap≤C := by
    intro v hv
    obtain ⟨u,hu,he⟩ := hSC hv
    have hueq : u=v := T.injective he
    exact hueq ▸ hu
  have hi:=invariant_comap_of_twisted_equivalence ρ σ α T hT S hS
  have hmap : (S.comap T.toLinearMap).map T.toLinearMap=S := by
    apply le_antisymm
    · rintro w ⟨v,hv,rfl⟩
      exact hv
    · intro w hw
      refine ⟨T.symm w,?_,T.apply_symm_apply w⟩
      change T (T.symm w)∈S
      rw [LinearEquiv.apply_symm_apply]
      exact hw
  rcases hC (S.comap T.toLinearMap) hle hi with hz|hz
  · left
    rw [hz,Submodule.map_bot] at hmap
    exact hmap.symm
  · right
    rw [hz] at hmap
    exact hmap.symm

end AMSPhysical
