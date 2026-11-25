import CompactHighestProjectionOrthogonal

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
  {q : ℝ} {n : ℕ} {lam : Fin n → ℤ}

/-- Actual adjoint partial channel map, constructed from the inverse physical
channel isometry and the actual target orthogonal projection. -/
def CompactHighestRealization.channelBackTransfer (hq : q≠0)
    (X : CompactHighestRealization q n V lam) (Y : CompactHighestRealization q n W lam) : W →ₗ[ℝ] V :=
  X.channel.subtype.comp ((X.transport hq Y).symm.toLinearMap.comp Y.channelProjection)

theorem CompactHighestRealization.channelTransfer_adjoint (hq : q≠0)
    (X : CompactHighestRealization q n V lam) (Y : CompactHighestRealization q n W lam) (v : V) (w : W) :
    Y.pairing (X.channelTransfer hq Y v) w=X.pairing v (X.channelBackTransfer hq Y w) := by
  let T:=X.transport hq Y
  have hM:=X.transport_isometry hq Y (X.channelProjection v) (T.symm (Y.channelProjection w))
  change X.channelPair (X.channelProjection v) (T.symm (Y.channelProjection w))=
    Y.channelPair (T (X.channelProjection v)) (T (T.symm (Y.channelProjection w))) at hM
  rw [LinearEquiv.apply_symm_apply] at hM
  calc
    _ = Y.channelPair (T (X.channelProjection v)) (Y.channelProjection w) :=
      Y.channelProjection_adjoint _ w
    _ = X.channelPair (X.channelProjection v) (T.symm (Y.channelProjection w)) := hM.symm
    _ = X.channelPair (T.symm (Y.channelProjection w)) (X.channelProjection v) := X.channelPair_symm _ _
    _ = X.pairing (T.symm (Y.channelProjection w)).val v :=
      (X.channelProjection_adjoint _ v).symm
    _ = _ := X.symmetric _ _

theorem CompactHighestRealization.channelBackTransfer_subtype (hq : q≠0)
    (X : CompactHighestRealization q n V lam) (Y : CompactHighestRealization q n W lam) (w : Y.channel) :
    X.channelBackTransfer hq Y w.val=((X.transport hq Y).symm w).val := by
  change ((X.transport hq Y).symm (Y.channelProjection w.val)).val=_
  rw [Y.channelProjection_subtype]

theorem CompactHighestRealization.channelBackTransfer_zero_of_orthogonal (hq : q≠0)
    (X : CompactHighestRealization q n V lam) (Y : CompactHighestRealization q n W lam) (w : W)
    (hw : ∀ v∈Y.channel,Y.pairing v w=0) : X.channelBackTransfer hq Y w=0 := by
  change ((X.transport hq Y).symm (Y.channelProjection w)).val=0
  rw [Y.channelProjection_zero_of_orthogonal w hw,map_zero]
  rfl

end AMSPhysical
#print axioms AMSPhysical.CompactHighestRealization.channelTransfer_adjoint
