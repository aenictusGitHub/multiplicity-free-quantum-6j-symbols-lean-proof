import CompactHighestChannelMetric
import CompactMetricAdjointIntertwiner

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W]
  {q : ℝ} {n : ℕ} {lam : Fin n → ℤ}

/-- Actual orthogonal channel projection in the compact physical metric. -/
def CompactHighestRealization.channelProjection (X : CompactHighestRealization q n V lam) :
    V →ₗ[ℝ] X.channel :=
  bilinearMetricAdjoint X.channelPair X.pairing X.channelPair_definite X.channel.subtype

theorem CompactHighestRealization.channelProjection_subtype (X : CompactHighestRealization q n V lam)
    (v : X.channel) : X.channelProjection v.val=v := by
  exact bilinearMetricAdjoint_isometry_leftInverse X.channelPair X.pairing X.channelPair_definite
    X.channelPair_symm X.symmetric X.channel.subtype (fun _ _ =>rfl) v

theorem CompactHighestRealization.channelProjection_intertwines (X : CompactHighestRealization q n V lam)
    (z : UqTypeA q n) (v : V) :
    X.channelProjection (X.action z v)=X.channelAction z (X.channelProjection v) := by
  exact compact_bilinearMetricAdjoint_intertwines q n X.channelAction X.action X.channelPair X.pairing
    X.channelCompact X.compact X.channelPair_definite X.channelPair_symm X.symmetric
    X.channel.subtype (fun _ _ =>rfl) z v

/-- The independently constructed full pair intertwiner selecting one common
highest channel. Its value is zero on the source orthogonal complement. -/
def CompactHighestRealization.channelTransfer (hq : q≠0) (X : CompactHighestRealization q n V lam)
    (Y : CompactHighestRealization q n W lam) : V →ₗ[ℝ] W :=
  Y.channel.subtype.comp ((X.transport hq Y).toLinearMap.comp X.channelProjection)

theorem CompactHighestRealization.channelTransfer_intertwines (hq : q≠0)
    (X : CompactHighestRealization q n V lam) (Y : CompactHighestRealization q n W lam)
    (z : UqTypeA q n) (v : V) :
    X.channelTransfer hq Y (X.action z v)=Y.action z (X.channelTransfer hq Y v) := by
  change (X.transport hq Y (X.channelProjection (X.action z v))).val=_
  rw [X.channelProjection_intertwines]
  exact X.transport_intertwines hq Y z (X.channelProjection v)

theorem CompactHighestRealization.channelTransfer_highest (hq : q≠0)
    (X : CompactHighestRealization q n V lam) (Y : CompactHighestRealization q n W lam) :
    X.channelTransfer hq Y X.highest=Y.highest := by
  have hp:=X.channelProjection_subtype ⟨X.highest,algebraCyclicSpan_self _ _⟩
  change (X.transport hq Y (X.channelProjection X.highest)).val=_
  rw [hp]
  exact X.transport_highest hq Y

theorem CompactHighestRealization.channelTransfer_mem (hq : q≠0)
    (X : CompactHighestRealization q n V lam) (Y : CompactHighestRealization q n W lam) (v : V) :
    X.channelTransfer hq Y v∈Y.channel :=
  (X.transport hq Y (X.channelProjection v)).property

theorem CompactHighestRealization.channelTransfer_ne_zero (hq : q≠0)
    (X : CompactHighestRealization q n V lam) (Y : CompactHighestRealization q n W lam) :
    X.channelTransfer hq Y≠0 := by
  intro he
  have hh:=X.channelTransfer_highest hq Y
  rw [he,LinearMap.zero_apply] at hh
  have hN:=Y.highestNorm
  rw [← hh,map_zero] at hN
  norm_num at hN

end AMSPhysical
#print axioms AMSPhysical.CompactHighestRealization.channelTransfer_intertwines
