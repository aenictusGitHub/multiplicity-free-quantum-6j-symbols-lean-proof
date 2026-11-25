import GlobalHighestCarrierCoherence

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  {q : ℝ} {n : ℕ} {lam : Fin n → ℤ}

/-- A full algebra intertwiner on an actual cyclic channel is its leading
highest scalar times canonical transport, on every vector in the channel. -/
theorem CompactHighestRealization.intertwiner_scalar_highest (hq : q≠0)
    (X : CompactHighestRealization q n V lam) (Y : CompactHighestRealization q n W lam)
    (F : V →ₗ[ℝ] W) (a : ℝ)
    (hF : ∀ z x,F (X.action z x)=Y.action z (F x))
    (hH : F X.highest=a • Y.highest) (x : X.channel) :
    F x.val=a • (X.transport hq Y x).val := by
  have he : F.comp X.channel.subtype =
      a • (Y.channel.subtype.comp (X.transport hq Y).toLinearMap) := by
    apply cyclic_intertwiner_unique X.action Y.action X.highest
    · intro z v
      exact hF z v.val
    · intro z v
      change a • ((X.transport hq Y) (X.channelAction z v)).val =
        Y.action z (a • ((X.transport hq Y) v).val)
      rw [map_smul]
      exact congrArg (fun w => a • w) (X.transport_intertwines hq Y z v)
    · change F X.highest = a • ((X.transport hq Y) ⟨X.highest,algebraCyclicSpan_self _ _⟩).val
      rw [X.transport_highest]
      exact hH
  exact DFunLike.congr_fun he x

theorem CompactHighestRealization.full_intertwiner_unique
    (X : CompactHighestRealization q n V lam) (hSpan : X.channel=⊤)
    (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W) (F G : V →ₗ[ℝ] W)
    (hF : ∀ z x,F (X.action z x)=σ z (F x))
    (hG : ∀ z x,G (X.action z x)=σ z (G x))
    (hH : F X.highest=G X.highest) : F=G := by
  have he : F.comp X.channel.subtype=G.comp X.channel.subtype := by
    apply cyclic_intertwiner_unique X.action σ X.highest
    · intro z v;exact hF z v.val
    · intro z v;exact hG z v.val
    · exact hH
  apply LinearMap.ext
  intro v
  have hv : v∈X.channel := by rw [hSpan];trivial
  exact DFunLike.congr_fun he ⟨v,hv⟩

end AMSPhysical
#print axioms AMSPhysical.CompactHighestRealization.intertwiner_scalar_highest
