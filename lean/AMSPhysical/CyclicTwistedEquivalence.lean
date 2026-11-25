import BilinearCyclic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {A V W : Type*} [Ring A] [Algebra ℝ A] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

theorem cyclic_map_of_twisted_equivalence (ρ : A →ₐ[ℝ] Module.End ℝ V) (σ : A →ₐ[ℝ] Module.End ℝ W)
    (α : A →ₐ[ℝ] A) (hα : Function.Surjective α) (T : V ≃ₗ[ℝ] W)
    (hT : ∀ z v,T (ρ z v)=σ (α z) (T v)) (v : V) :
    (algebraCyclicSpan ρ v).map T.toLinearMap=algebraCyclicSpan σ (T v) := by
  unfold algebraCyclicSpan
  rw [Submodule.map_span]
  congr 1
  apply Set.ext
  intro w
  constructor
  · rintro ⟨x,⟨z,rfl⟩,rfl⟩
    exact ⟨α z,(hT z v).symm⟩
  · rintro ⟨z,rfl⟩
    obtain ⟨u,rfl⟩ := hα z
    exact ⟨ρ u v,⟨u,rfl⟩,hT u v⟩

theorem invariant_map_of_twisted_equivalence (ρ : A →ₐ[ℝ] Module.End ℝ V) (σ : A →ₐ[ℝ] Module.End ℝ W)
    (α : A →ₐ[ℝ] A) (hα : Function.Surjective α) (T : V ≃ₗ[ℝ] W)
    (hT : ∀ z v,T (ρ z v)=σ (α z) (T v)) (S : Submodule ℝ V) (hS : algebraInvariant ρ S) :
    algebraInvariant σ (S.map T.toLinearMap) := by
  intro z w hw
  obtain ⟨v,hv,rfl⟩ := hw
  obtain ⟨u,rfl⟩ := hα z
  exact ⟨ρ u v,hS u v hv,hT u v⟩

theorem invariant_comap_of_twisted_equivalence (ρ : A →ₐ[ℝ] Module.End ℝ V) (σ : A →ₐ[ℝ] Module.End ℝ W)
    (α : A →ₐ[ℝ] A) (T : V ≃ₗ[ℝ] W)
    (hT : ∀ z v,T (ρ z v)=σ (α z) (T v)) (S : Submodule ℝ W) (hS : algebraInvariant σ S) :
    algebraInvariant ρ (S.comap T.toLinearMap) := by
  intro z v hv
  change T (ρ z v)∈S
  rw [hT]
  exact hS (α z) (T v) hv

end AMSPhysical
