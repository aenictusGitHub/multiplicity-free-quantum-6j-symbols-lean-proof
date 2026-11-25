import GlobalScalarHighestTransport
import CompactHighestFullEmbedding
import CompactHighestOnChannel

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {V W Z : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [AddCommGroup Z] [Module ℝ Z]
  {q : ℝ} {n : ℕ} {lam : Fin n → ℤ}

theorem CompactHighestRealization.fullEmbedding_self (hq : q≠0)
    (X : CompactHighestRealization q n V lam) (hX : X.channel=⊤) :
    X.fullEmbedding hq hX X=LinearMap.id := by
  apply X.full_intertwiner_unique hX X.action
  · exact X.fullEmbedding_intertwines hq hX X
  · intro z x;rfl
  · exact X.fullEmbedding_highest hq hX X

theorem CompactHighestRealization.fullEmbedding_comp (hq : q≠0)
    (X : CompactHighestRealization q n V lam) (hX : X.channel=⊤)
    (Y : CompactHighestRealization q n W lam) (hY : Y.channel=⊤)
    (T : CompactHighestRealization q n Z lam) :
    (Y.fullEmbedding hq hY T).comp (X.fullEmbedding hq hX Y)=X.fullEmbedding hq hX T := by
  apply X.full_intertwiner_unique hX T.action
  · intro z x
    simp only [LinearMap.comp_apply]
    rw [X.fullEmbedding_intertwines hq hX Y,Y.fullEmbedding_intertwines hq hY T]
  · exact X.fullEmbedding_intertwines hq hX T
  · simp only [LinearMap.comp_apply,X.fullEmbedding_highest hq hX Y,Y.fullEmbedding_highest hq hY T,
      X.fullEmbedding_highest hq hX T]

end AMSPhysical
#print axioms AMSPhysical.CompactHighestRealization.fullEmbedding_comp
