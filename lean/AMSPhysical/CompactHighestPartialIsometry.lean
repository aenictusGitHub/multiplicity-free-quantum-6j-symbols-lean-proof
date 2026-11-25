import CompactHighestBackTransfer
import CompactHighestTrace

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
noncomputable section
namespace AMSPhysical
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
  {q:ℝ} {n:ℕ} {lam:Fin n → ℤ}

theorem CompactHighestRealization.channelBackTransfer_transfer (hq:q≠0)
    (X:CompactHighestRealization q n V lam) (Y:CompactHighestRealization q n W lam) (v:V) :
    X.channelBackTransfer hq Y (X.channelTransfer hq Y v)=(X.channelProjection v).val := by
  change X.channelBackTransfer hq Y ((X.transport hq Y) (X.channelProjection v)).val=_
  rw [X.channelBackTransfer_subtype,LinearEquiv.symm_apply_apply]

theorem CompactHighestRealization.channelTransfer_metric_projection (hq:q≠0)
    (X:CompactHighestRealization q n V lam) (Y:CompactHighestRealization q n W lam) (v w:V) :
    Y.pairing (X.channelTransfer hq Y v) (X.channelTransfer hq Y w)=
      X.pairing v (X.channelProjection w).val := by
  rw [X.channelTransfer_adjoint,X.channelBackTransfer_transfer]

/-- The trace of the actual projected action is exactly the trace on the
actual irreducible channel; no dimension formula is assumed. -/
theorem CompactHighestRealization.channelProjection_trace
    (X:CompactHighestRealization q n V lam) (z:UqTypeA q n) :
    LinearMap.trace ℝ V (X.channel.subtype.comp (X.channelProjection.comp (X.action z)))=
      LinearMap.trace ℝ X.channel (X.channelAction z) := by
  rw [LinearMap.trace_comp_comm']
  have he:X.channelProjection.comp ((X.action z).comp X.channel.subtype)=X.channelAction z := by
    apply LinearMap.ext
    intro v
    change X.channelProjection (X.action z v.val)=_
    rw [X.channelProjection_intertwines,X.channelProjection_subtype]
  simpa only [LinearMap.comp_assoc] using congrArg (LinearMap.trace ℝ X.channel) he

end AMSPhysical
#print axioms AMSPhysical.CompactHighestRealization.channelProjection_trace
