import QuantumMixedIrreducible
import InvariantRepresentationRestriction

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- The actual finite-dimensional full algebra representation on the
constructed mixed irreducible channel, as an invariant orbit submodule. -/
def mixedChannelRepresentation (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n r a b : ℕ) :
    UqTypeA q n →ₐ[ℝ] Module.End ℝ (mixedChannelSubmodule q hq hD n r a b) :=
  invariantRepresentationRestriction (A:=UqTypeA q n)
    (V:=quantumOccupationSpace ℝ (Fin (n+1)) (r+a) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (r+b))
    (typeAMixedTensor q hq hD n (r+a) (r+b))
    (mixedChannelSubmodule q hq hD n r a b) (mixedChannelSubmodule_invariant q hq hD n r a b)

def mixedChannelHighest (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n r a b : ℕ) :
    mixedChannelSubmodule q hq hD n r a b :=
  ⟨mixedHighestVector q n r a b,algebraCyclicSpan_self _ _⟩

theorem mixedChannelHighest_E_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n r a b : ℕ) (i : Fin n) :
    mixedChannelRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n r a b
      (typeAAlgebraGenerator q n i 0)
      (mixedChannelHighest q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n r a b)=0 := by
  apply Subtype.ext
  change typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (r+a) (r+b)
    (typeAAlgebraGenerator q n i 0) (mixedHighestVector q n r a b)=0
  exact mixedHighestVector_E_zero q hq hq1 n r a b i

theorem mixedChannelHighest_K (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n r a b : ℕ) (i : Fin n) :
    mixedChannelRepresentation q hq hD n r a b (typeAAlgebraGenerator q n i 2)
      (mixedChannelHighest q hq hD n r a b)=
      q^(mixedHighestDynkin n a b i) • mixedChannelHighest q hq hD n r a b := by
  apply Subtype.ext
  change typeAMixedTensor q hq hD n (r+a) (r+b) (typeAAlgebraGenerator q n i 2)
    (mixedHighestVector q n r a b)=q^(mixedHighestDynkin n a b i) • mixedHighestVector q n r a b
  exact mixedHighestVector_K q hq hD n r a b i

end AMSPhysical
#print axioms AMSPhysical.mixedChannelRepresentation
