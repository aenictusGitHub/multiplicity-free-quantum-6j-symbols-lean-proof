import BilinearOrthogonalSum
import InvariantRepresentationRestriction

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical
variable {A V I : Type*} [Ring A] [Algebra ℝ A] [AddCommGroup V] [Module ℝ V] [Fintype I]

theorem submoduleFamilySum_intertwines (ρ : A →ₐ[ℝ] Module.End ℝ V)
    (S : I → Submodule ℝ V) (hS : ∀ i,algebraInvariant ρ (S i))
    (z : A) (x : ∀ i,S i) :
    submoduleFamilySum S (fun i => invariantRepresentationRestriction ρ (S i) (hS i) z (x i))=
      ρ z (submoduleFamilySum S x) := by
  change (∑ i,ρ z (x i).val)=ρ z (∑ i,(x i).val)
  rw [map_sum]

end AMSPhysical
