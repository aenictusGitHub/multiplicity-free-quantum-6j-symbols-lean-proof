import CompactTypeAPair
import InvariantRepresentationRestriction

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def restrictedBilinearPair (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (S : Submodule ℝ V) : S →ₗ[ℝ] S →ₗ[ℝ] ℝ :=
  (B.comp S.subtype).compl₂ S.subtype

theorem restrictedBilinearPair_symm (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hB : ∀ v w,B v w=B w v)
    (S : Submodule ℝ V) (v w : S) : restrictedBilinearPair B S v w=restrictedBilinearPair B S w v :=
  hB v.val w.val

theorem restrictedBilinearPair_definite (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hB : ∀ v,B v v=0 → v=0)
    (S : Submodule ℝ V) (v : S) (h : restrictedBilinearPair B S v v=0) : v=0 :=
  Subtype.ext (hB v.val h)

/-- The actual restricted channel action inherits all compact generator
adjoints from its proved invariant ambient representation. -/
theorem compactTypeAPair_restriction (q : ℝ) (n : ℕ) (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hB : IsCompactTypeAPair q n B ρ)
    (S : Submodule ℝ V) (hS : algebraInvariant ρ S) :
    IsCompactTypeAPair q n (restrictedBilinearPair B S) (invariantRepresentationRestriction ρ S hS) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i v w
    exact hB.adjE i v.val w.val
  · intro i v w
    exact hB.adjF i v.val w.val
  · intro i v w
    exact hB.adjK i v.val w.val
  · intro i v w
    exact hB.adjKi i v.val w.val

end AMSPhysical
