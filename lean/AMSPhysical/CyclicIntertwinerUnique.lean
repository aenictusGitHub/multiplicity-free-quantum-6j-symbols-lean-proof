import InvariantRepresentationRestriction

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical
variable {A V W : Type*} [Ring A] [Algebra ℝ A] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- Full algebra intertwiners from a constructed cyclic channel are determined
by their value on its actual highest generator. -/
theorem cyclic_intertwiner_unique (ρ : A →ₐ[ℝ] Module.End ℝ V) (τ : A →ₐ[ℝ] Module.End ℝ W) (v : V)
    (f g : algebraCyclicSpan ρ v →ₗ[ℝ] W)
    (hf : ∀ z x,f (invariantRepresentationRestriction ρ (algebraCyclicSpan ρ v)
      (algebraCyclicSpan_invariant ρ v) z x)=τ z (f x))
    (hg : ∀ z x,g (invariantRepresentationRestriction ρ (algebraCyclicSpan ρ v)
      (algebraCyclicSpan_invariant ρ v) z x)=τ z (g x))
    (hv : f ⟨v,algebraCyclicSpan_self ρ v⟩=g ⟨v,algebraCyclicSpan_self ρ v⟩) : f=g := by
  let C := algebraCyclicSpan ρ v
  let S := (LinearMap.eqLocus f g).map C.subtype
  have hS : algebraInvariant ρ S := by
    rintro z x ⟨u,hu,rfl⟩
    refine ⟨invariantRepresentationRestriction ρ C (algebraCyclicSpan_invariant ρ v) z u,?_,rfl⟩
    change f (invariantRepresentationRestriction ρ C (algebraCyclicSpan_invariant ρ v) z u)=
      g (invariantRepresentationRestriction ρ C (algebraCyclicSpan_invariant ρ v) z u)
    rw [hf,hg]
    exact congrArg (τ z) hu
  have hvs : v∈S := ⟨⟨v,algebraCyclicSpan_self ρ v⟩,hv,rfl⟩
  have hCS := algebraCyclicSpan_minimal ρ v S hS hvs
  apply LinearMap.ext
  intro x
  have hm : x.val∈S := hCS x.property
  obtain ⟨u,hu,he⟩ := hm
  have hux : u=x := Subtype.ext he
  simpa only [hux] using hu

end AMSPhysical
#print axioms AMSPhysical.cyclic_intertwiner_unique
