import InvariantRepresentationRestriction
import Mathlib.LinearAlgebra.Trace

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace AMSPhysical
variable {A V : Type*} [Ring A] [Algebra ℝ A] [AddCommGroup V] [Module ℝ V]

theorem trace_invariantRestriction_congr (ρ : A →ₐ[ℝ] Module.End ℝ V) (S T : Submodule ℝ V)
    (hS : algebraInvariant ρ S) (hT : algebraInvariant ρ T) (h : S=T) (z : A) :
    LinearMap.trace ℝ S (invariantRepresentationRestriction ρ S hS z)=
      LinearMap.trace ℝ T (invariantRepresentationRestriction ρ T hT z) := by
  subst T
  rfl

end AMSPhysical
