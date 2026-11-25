import BilinearCyclic
import PreservingEndAlgebra

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {A V : Type*} [Ring A] [Algebra ℝ A] [AddCommGroup V] [Module ℝ V]

/-- Full algebra representation on a proved invariant subspace. -/
def invariantRepresentationRestriction (ρ : A →ₐ[ℝ] Module.End ℝ V)
    (S : Submodule ℝ V) (hS : algebraInvariant ρ S) : A →ₐ[ℝ] Module.End ℝ S :=
  (restrictPreservingEnd S).comp (ρ.codRestrict (preservingEndAlgebra S) hS)

theorem invariantRepresentationRestriction_apply (ρ : A →ₐ[ℝ] Module.End ℝ V)
    (S : Submodule ℝ V) (hS : algebraInvariant ρ S) (z : A) (v : S) :
    (invariantRepresentationRestriction ρ S hS z v).val=ρ z v.val := rfl

end AMSPhysical
#print axioms AMSPhysical.invariantRepresentationRestriction
