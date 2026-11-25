import CompactHighestTrace
import CompactInvariantRestriction

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace AMSPhysical
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {q : ℝ} {n : ℕ} {lam : Fin n → ℤ}

def CompactHighestRealization.channelPair (X : CompactHighestRealization q n V lam) :
    X.channel →ₗ[ℝ] X.channel →ₗ[ℝ] ℝ := restrictedBilinearPair X.pairing X.channel

theorem CompactHighestRealization.channelPair_symm (X : CompactHighestRealization q n V lam)
    (v w : X.channel) : X.channelPair v w=X.channelPair w v := X.symmetric v.val w.val

theorem CompactHighestRealization.channelPair_definite (X : CompactHighestRealization q n V lam)
    (v : X.channel) (h : X.channelPair v v=0) : v=0 := Subtype.ext (X.definite v.val h)

theorem CompactHighestRealization.channelCompact (X : CompactHighestRealization q n V lam) :
    IsCompactTypeAPair q n X.channelPair X.channelAction :=
  compactTypeAPair_restriction q n X.action X.pairing X.compact X.channel
    (algebraCyclicSpan_invariant X.action X.highest)

end AMSPhysical
