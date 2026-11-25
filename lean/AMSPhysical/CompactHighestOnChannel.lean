import GlobalHighestCarrierCoherence

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  {q : ℝ} {n : ℕ} {lam : Fin n → ℤ}

def CompactHighestRealization.onChannel (X : CompactHighestRealization q n V lam) :
    CompactHighestRealization q n X.channel lam where
  action := X.channelAction
  pairing := X.channelPair
  highest := ⟨X.highest,algebraCyclicSpan_self _ _⟩
  compact := X.channelCompact
  symmetric := X.channelPair_symm
  definite := X.channelPair_definite
  highestE := by intro i;apply Subtype.ext;exact X.highestE i
  highestK := by intro i;apply Subtype.ext;exact X.highestK i
  highestNorm := X.highestNorm

/-- Restriction to the actual cyclic irrep is a complete highest carrier.
It can therefore be used as a genuine common representation object. -/
theorem CompactHighestRealization.onChannel_complete (X : CompactHighestRealization q n V lam) :
    X.onChannel.channel=⊤ := by
  have he : X.onChannel.channel.map X.channel.subtype=X.channel := by
    unfold channel algebraCyclicSpan
    rw [Submodule.map_span]
    congr 1
    ext v
    constructor
    · rintro ⟨y,⟨z,rfl⟩,rfl⟩
      exact ⟨z,rfl⟩
    · rintro ⟨z,rfl⟩
      exact ⟨X.onChannel.action z X.onChannel.highest,⟨z,rfl⟩,rfl⟩
  apply top_unique
  intro x hx
  have hm : x.val∈X.onChannel.channel.map X.channel.subtype := by
    rw [he]
    exact x.property
  obtain ⟨y,hy,heq⟩:=hm
  have heq' : y=x := Subtype.ext heq
  rwa [heq'] at hy

theorem CompactHighestRealization.transport_highest_functional (hq : q≠0)
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (X : CompactHighestRealization q n V lam) (Y : CompactHighestRealization q n W lam)
    (x : X.channel) :
    Y.pairing Y.highest (X.transport hq Y x).val = X.pairing X.highest x.val := by
  have he:=X.transport_isometry hq Y ⟨X.highest,algebraCyclicSpan_self _ _⟩ x
  rw [X.transport_highest] at he
  exact he.symm

end AMSPhysical
#print axioms AMSPhysical.CompactHighestRealization.onChannel_complete
