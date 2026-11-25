import QuantumMixedChannelRepresentation
import RestrictedIrreducible

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- Irreducibility on the actual restricted channel carrier itself. -/
theorem mixedChannelRepresentation_irreducible (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n r a b : ℕ) (hn : 0<n)
    (S : Submodule ℝ (mixedChannelSubmodule q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n r a b))
    (hS : ∀ z : UqTypeA q n,∀ v∈S,
      mixedChannelRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n r a b z v∈S) :
    S=⊥ ∨ S=⊤ :=
  restriction_irreducible (A:=UqTypeA q n)
    (V:=quantumOccupationSpace ℝ (Fin (n+1)) (r+a) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (r+b))
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (r+a) (r+b))
    (mixedChannelSubmodule q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n r a b)
    (mixedChannelSubmodule_invariant q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n r a b)
    (mixedChannelSubmodule_irreducible q hq hq1 n r a b hn) S
    (by simpa only [mixedChannelRepresentation,algebraInvariant] using hS)

end AMSPhysical
#print axioms AMSPhysical.mixedChannelRepresentation_irreducible
