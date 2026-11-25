import CompactHighestRealization
import InvariantRepresentationRestriction
import Mathlib.LinearAlgebra.Trace

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

theorem trace_intertwined_equiv (f : Module.End ℝ V) (g : Module.End ℝ W) (e : V ≃ₗ[ℝ] W)
    (h : ∀ v,e (f v)=g (e v)) : LinearMap.trace ℝ V f=LinearMap.trace ℝ W g := by
  have he : e.conj f=g := by
    apply LinearMap.ext
    intro w
    change e (f (e.symm w))=g w
    rw [h,LinearEquiv.apply_symm_apply]
  rw [← he,LinearMap.trace_conj']

def CompactHighestRealization.channelAction {q : ℝ} {n : ℕ} {lam : Fin n → ℤ}
    (X : CompactHighestRealization q n V lam) : UqTypeA q n →ₐ[ℝ] Module.End ℝ X.channel :=
  invariantRepresentationRestriction X.action X.channel (algebraCyclicSpan_invariant X.action X.highest)

theorem CompactHighestRealization.trace_transport {q : ℝ} {n : ℕ} {lam : Fin n → ℤ}
    (hq : q≠0) (X : CompactHighestRealization q n V lam) (Y : CompactHighestRealization q n W lam)
    (z : UqTypeA q n) :
    LinearMap.trace ℝ X.channel (X.channelAction z)=LinearMap.trace ℝ Y.channel (Y.channelAction z) := by
  apply trace_intertwined_equiv (X.channelAction z) (Y.channelAction z) (CompactHighestRealization.transport hq X Y)
  intro v
  apply Subtype.ext
  exact CompactHighestRealization.transport_intertwines hq X Y z v

end AMSPhysical
