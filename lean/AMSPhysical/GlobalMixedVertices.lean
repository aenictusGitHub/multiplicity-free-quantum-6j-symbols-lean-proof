import GlobalHighestCarrierCoherence
import QuantumMixedCanonicalClebsch
import QuantumReverseCanonicalClebsch

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

/-- All mixed-channel realizations use exactly coherent highest transport,
including zero contractions and arbitrary nonnegative highest labels. -/
theorem mixedCanonicalTransport_comp (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b r s t : ℕ)
    (x : normalizedMixedChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n r a b) :
    mixedCanonicalTransport q hq hq1 n hn a b s t
      (mixedCanonicalTransport q hq hq1 n hn a b r s x) =
      mixedCanonicalTransport q hq hq1 n hn a b r t x := by
  exact CompactHighestRealization.transport_comp (ne_of_gt hq)
    (mixedHighestRealization q hq hq1 n hn r a b)
    (mixedHighestRealization q hq hq1 n hn s a b)
    (mixedHighestRealization q hq hq1 n hn t a b) x

/-- Passing through any forward realization before reversing the order
has exactly the same phase as direct transport from the fixed carrier. -/
theorem mixedCanonicalTransport_reverse_coherent (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b r s : ℕ)
    (x : normalizedMixedChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n 0 a b) :
    (mixedHighestRealization q hq hq1 n hn r a b).transport (ne_of_gt hq)
      (reverseMixedHighestRealization q hq hq1 n hn s a b)
      (mixedCanonicalTransport q hq hq1 n hn a b 0 r x) =
      reverseMixedCanonicalTransport q hq hq1 n hn a b s x := by
  exact CompactHighestRealization.transport_comp (ne_of_gt hq)
    (mixedHighestRealization q hq hq1 n hn 0 a b)
    (mixedHighestRealization q hq hq1 n hn r a b)
    (reverseMixedHighestRealization q hq hq1 n hn s a b) x

end AMSPhysical
#print axioms AMSPhysical.mixedCanonicalTransport_comp
#print axioms AMSPhysical.mixedCanonicalTransport_reverse_coherent
