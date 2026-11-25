import TraceRetractionDecomposition
import InvariantRepresentationRestriction

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
variable {A I V : Type*} [Ring A] [Algebra ℝ A] [Fintype I] [DecidableEq I]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- Trace additivity follows from the ACTUAL complete direct-sum equivalence
and invariant restrictions. No character or fusion-rule identity is assumed. -/
theorem trace_invariant_family (ρ : A →ₐ[ℝ] Module.End ℝ V) (S : I → Submodule ℝ V)
    (hS : ∀ i,algebraInvariant ρ (S i)) (e : (∀ i,S i) ≃ₗ[ℝ] V)
    (he : e.toLinearMap=submoduleFamilySum S) (z : A) :
    LinearMap.trace ℝ V (ρ z)=
      ∑ i,LinearMap.trace ℝ (S i) (invariantRepresentationRestriction ρ (S i) (hS i) z) := by
  apply trace_decomposition_of_retractions (fun i =>(S i).subtype) (familyEquivProjection S e)
    (familyEquivProjection_resolution S e he) (familyEquivProjection_subtype S e he)
    (ρ z) (fun i =>invariantRepresentationRestriction ρ (S i) (hS i) z)
  intro i
  apply LinearMap.ext
  intro v
  rfl

end AMSPhysical
