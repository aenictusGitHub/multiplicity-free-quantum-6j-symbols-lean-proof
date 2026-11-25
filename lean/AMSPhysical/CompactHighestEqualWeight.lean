import CompactHighestRealization

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace AMSPhysical
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
variable {q : ℝ} {n : ℕ} {lam mu : Fin n → ℤ}

def CompactHighestRealization.transportEqualWeight (hq : q≠0)
    (X : CompactHighestRealization q n V lam) (Y : CompactHighestRealization q n W mu)
    (h : lam=mu) : X.channel ≃ₗ[ℝ] Y.channel := by
  subst mu
  exact CompactHighestRealization.transport hq X Y

theorem CompactHighestRealization.transportEqualWeight_isometry (hq : q≠0)
    (X : CompactHighestRealization q n V lam) (Y : CompactHighestRealization q n W mu)
    (h : lam=mu) (v w : X.channel) :
    X.pairing v.val w.val=Y.pairing
      (CompactHighestRealization.transportEqualWeight hq X Y h v).val
      (CompactHighestRealization.transportEqualWeight hq X Y h w).val := by
  subst mu
  exact CompactHighestRealization.transport_isometry hq X Y v w

theorem CompactHighestRealization.transportEqualWeight_intertwines (hq : q≠0)
    (X : CompactHighestRealization q n V lam) (Y : CompactHighestRealization q n W mu)
    (h : lam=mu) (z : UqTypeA q n) (v : X.channel) :
    (CompactHighestRealization.transportEqualWeight hq X Y h
      ⟨X.action z v.val,algebraCyclicSpan_invariant _ _ z v.val v.property⟩).val=
      Y.action z (CompactHighestRealization.transportEqualWeight hq X Y h v).val := by
  subst mu
  exact CompactHighestRealization.transport_intertwines hq X Y z v

end AMSPhysical
