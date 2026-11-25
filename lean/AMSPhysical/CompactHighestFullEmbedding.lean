import CompactHighestRealization

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  {q : ℝ} {n : ℕ} {lam : Fin n → ℤ}

def CompactHighestRealization.fullEmbedding (hq : q≠0)
    (X : CompactHighestRealization q n V lam) (hSpan : X.channel=⊤)
    (Y : CompactHighestRealization q n W lam) : V →ₗ[ℝ] W :=
  Y.channel.subtype.comp ((X.transport hq Y).toLinearMap.comp
    (LinearMap.codRestrict X.channel LinearMap.id (fun v =>by rw [hSpan];trivial)))

theorem CompactHighestRealization.fullEmbedding_isometry (hq : q≠0)
    (X : CompactHighestRealization q n V lam) (hSpan : X.channel=⊤)
    (Y : CompactHighestRealization q n W lam) (v w : V) :
    Y.pairing (X.fullEmbedding hq hSpan Y v) (X.fullEmbedding hq hSpan Y w)=X.pairing v w := by
  exact (X.transport_isometry hq Y ⟨v,by rw [hSpan];trivial⟩ ⟨w,by rw [hSpan];trivial⟩).symm

theorem CompactHighestRealization.fullEmbedding_intertwines (hq : q≠0)
    (X : CompactHighestRealization q n V lam) (hSpan : X.channel=⊤)
    (Y : CompactHighestRealization q n W lam) (z : UqTypeA q n) (v : V) :
    X.fullEmbedding hq hSpan Y (X.action z v)=Y.action z (X.fullEmbedding hq hSpan Y v) := by
  exact X.transport_intertwines hq Y z ⟨v,by rw [hSpan];trivial⟩

theorem CompactHighestRealization.fullEmbedding_highest (hq : q≠0)
    (X : CompactHighestRealization q n V lam) (hSpan : X.channel=⊤)
    (Y : CompactHighestRealization q n W lam) :
    X.fullEmbedding hq hSpan Y X.highest=Y.highest :=
  X.transport_highest hq Y

theorem CompactHighestRealization.fullEmbedding_mem_channel (hq : q≠0)
    (X : CompactHighestRealization q n V lam) (hSpan : X.channel=⊤)
    (Y : CompactHighestRealization q n W lam) (v : V) :
    X.fullEmbedding hq hSpan Y v∈Y.channel :=
  (X.transport hq Y ⟨v,by rw [hSpan];trivial⟩).property

end AMSPhysical
#print axioms AMSPhysical.CompactHighestRealization.fullEmbedding_isometry
#print axioms AMSPhysical.CompactHighestRealization.fullEmbedding_intertwines
