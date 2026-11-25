import CompactHighestChannelTransfer

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] {q : ℝ} {n : ℕ} {lam : Fin n → ℤ}

theorem CompactHighestRealization.channelProjection_adjoint (X : CompactHighestRealization q n V lam)
    (u : X.channel) (v : V) : X.pairing u.val v=X.channelPair u (X.channelProjection v) :=
  bilinearMetricAdjoint_adjoint X.channelPair X.pairing X.channelPair_definite X.channelPair_symm X.symmetric
    X.channel.subtype u v

theorem CompactHighestRealization.channelProjection_zero_of_orthogonal
    (X : CompactHighestRealization q n V lam) (v : V)
    (hv : ∀ w∈X.channel,X.pairing w v=0) : X.channelProjection v=0 := by
  apply X.channelPair_definite
  rw [← X.channelProjection_adjoint]
  exact hv _ (X.channelProjection v).property

theorem CompactHighestRealization.channelTransfer_zero_of_orthogonal (hq : q≠0)
    (X : CompactHighestRealization q n V lam) (Y : CompactHighestRealization q n W lam) (v : V)
    (hv : ∀ w∈X.channel,X.pairing w v=0) : X.channelTransfer hq Y v=0 := by
  change (X.transport hq Y (X.channelProjection v)).val=0
  rw [X.channelProjection_zero_of_orthogonal v hv,map_zero]
  rfl

end AMSPhysical
#print axioms AMSPhysical.CompactHighestRealization.channelProjection_zero_of_orthogonal
