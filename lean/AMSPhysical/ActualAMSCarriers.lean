import ActualHighestCarrier
import GlobalTypeIILeftVertices
import GlobalMixedPairTransfers
import OppositeHighestRealization
import QuantumSymmetricHighestRealization

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

def actualSymmetricCarrier (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n p : ℕ) :=
  ActualHighestCarrier.ofWhole (symmetricHighestRealization q hq hq1 n p)
    (symmetricHighestRealization_channel_top q hq hq1 n p)

def actualOppositeCarrier (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (_hn : 0<n) (s : ℕ) :=
  ActualHighestCarrier.ofWhole (oppositeHighestRealization q hq hq1 n s)
    (oppositeHighestRealization_channel_top q hq hq1 n s)

def actualMixedCarrier (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (p s : ℕ) :=
  ActualHighestCarrier.ofChannel (globalMixedPairRealization q hq hq1 n hn p s 0)

def actualTwoRowCarrier (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (S r : ℕ) (hr : 2*r≤S) :=
  ActualHighestCarrier.ofChannel (globalTwoRowCarrier q hq hq1 n hn S r hr)

/-- The mixed and pure-symmetric names are the same actual object at s=0. -/
theorem actualMixed_symmetric_alias (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (p : ℕ) :
    (actualMixedCarrier q hq hq1 n hn p 0).irrep=(actualSymmetricCarrier q hq hq1 n p).irrep :=
  Subtype.ext rfl

theorem actualMixed_opposite_alias (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (s : ℕ) :
    (actualMixedCarrier q hq hq1 n hn 0 s).irrep=(actualOppositeCarrier q hq hq1 n hn s).irrep :=
  Subtype.ext rfl

end AMSPhysical
#print axioms AMSPhysical.actualMixed_symmetric_alias
