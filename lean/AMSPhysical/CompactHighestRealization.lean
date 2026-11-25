import HighestCyclicIntertwining

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- A collection of already-proved data for an actual unit-normalized compact
highest realization; instances below supply every field by construction. -/
structure CompactHighestRealization (q : ℝ) (n : ℕ) (V : Type*) [AddCommGroup V] [Module ℝ V]
    (lam : Fin n → ℤ) where
  action : UqTypeA q n →ₐ[ℝ] Module.End ℝ V
  pairing : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  highest : V
  compact : IsCompactTypeAPair q n pairing action
  symmetric : ∀ v w,pairing v w=pairing w v
  definite : ∀ v,pairing v v=0 → v=0
  highestE : ∀ i,action (typeAAlgebraGenerator q n i 0) highest=0
  highestK : ∀ i,action (typeAAlgebraGenerator q n i 2) highest=q^(lam i) • highest
  highestNorm : pairing highest highest=1

variable {q : ℝ} {n : ℕ} {lam : Fin n → ℤ}

def CompactHighestRealization.channel (X : CompactHighestRealization q n V lam) : Submodule ℝ V :=
  algebraCyclicSpan X.action X.highest

open CompactHighestRealization

def CompactHighestRealization.transport (hq : q≠0) (X : CompactHighestRealization q n V lam)
    (Y : CompactHighestRealization q n W lam) : X.channel ≃ₗ[ℝ] Y.channel :=
  highestCyclicTransport q hq n X.action Y.action X.pairing Y.pairing X.compact Y.compact
    X.symmetric Y.symmetric X.definite Y.definite X.highest Y.highest lam
    X.highestE Y.highestE X.highestK Y.highestK (X.highestNorm.trans Y.highestNorm.symm)

theorem CompactHighestRealization.transport_isometry (hq : q≠0) (X : CompactHighestRealization q n V lam)
    (Y : CompactHighestRealization q n W lam) (v w : X.channel) :
    X.pairing v.val w.val=Y.pairing (transport hq X Y v).val (transport hq X Y w).val :=
  highestCyclicTransport_isometry q hq n X.action Y.action X.pairing Y.pairing X.compact Y.compact
    X.symmetric Y.symmetric X.definite Y.definite X.highest Y.highest lam
    X.highestE Y.highestE X.highestK Y.highestK (X.highestNorm.trans Y.highestNorm.symm) v w

theorem CompactHighestRealization.transport_intertwines (hq : q≠0) (X : CompactHighestRealization q n V lam)
    (Y : CompactHighestRealization q n W lam) (z : UqTypeA q n) (v : X.channel) :
    (transport hq X Y ⟨X.action z v.val,algebraCyclicSpan_invariant _ _ z v.val v.property⟩).val=
      Y.action z (transport hq X Y v).val :=
  highestCyclicTransport_intertwines q hq n X.action Y.action X.pairing Y.pairing X.compact Y.compact
    X.symmetric Y.symmetric X.definite Y.definite X.highest Y.highest lam
    X.highestE Y.highestE X.highestK Y.highestK (X.highestNorm.trans Y.highestNorm.symm) z v

theorem CompactHighestRealization.transport_highest (hq : q≠0) (X : CompactHighestRealization q n V lam)
    (Y : CompactHighestRealization q n W lam) :
    (transport hq X Y ⟨X.highest,algebraCyclicSpan_self _ _⟩).val=Y.highest :=
  highestCyclicTransport_highest q hq n X.action Y.action X.pairing Y.pairing X.compact Y.compact
    X.symmetric Y.symmetric X.definite Y.definite X.highest Y.highest lam
    X.highestE Y.highestE X.highestK Y.highestK (X.highestNorm.trans Y.highestNorm.symm)

end AMSPhysical
