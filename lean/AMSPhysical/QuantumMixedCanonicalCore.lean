import HighestCyclicIntertwining
import QuantumMixedNormalization
import QuantumMixedCompact

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 120000

noncomputable section
namespace AMSPhysical
attribute [local irreducible] typeAMixedTensor mixedTensorBilin normalizedMixedHighestVector
open scoped TensorProduct

abbrev normalizedMixedChannel (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n r a b : ℕ) :
    Submodule ℝ (quantumOccupationSpace ℝ (Fin (n+1)) (r+a) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (r+b)) :=
  algebraCyclicSpan
    (V:=quantumOccupationSpace ℝ (Fin (n+1)) (r+a) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (r+b))
    (typeAMixedTensor q hq hD n (r+a) (r+b)) (normalizedMixedHighestVector q n r a b)

/-- Canonical isometric identification of arbitrary-rank mixed channels
with the same highest weight in different symmetric tensor realizations. -/
def mixedCanonicalTransport (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (a b r s : ℕ) :
    normalizedMixedChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n r a b ≃ₗ[ℝ]
      normalizedMixedChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n s a b :=
  by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) (r+a) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (r+b)
  let W := quantumOccupationSpace ℝ (Fin (n+1)) (s+a) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (s+b)
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  exact highestCyclicTransport
    (V:=V) (W:=W)
    q (ne_of_gt hq) n
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (r+a) (r+b))
    (typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (s+a) (s+b))
    (mixedTensorBilin q n (r+a) (r+b)) (mixedTensorBilin q n (s+a) (s+b))
    (typeAMixedTensor_compact q hq hq1 n (r+a) (r+b))
    (typeAMixedTensor_compact q hq hq1 n (s+a) (s+b))
    (mixedTensorBilin_symm q n (r+a) (r+b)) (mixedTensorBilin_symm q n (s+a) (s+b))
    (mixedTensorBilin_definite q hq n (r+a) (r+b)) (mixedTensorBilin_definite q hq n (s+a) (s+b))
    (normalizedMixedHighestVector q n r a b) (normalizedMixedHighestVector q n s a b)
    (mixedHighestDynkin n a b)
    (normalizedMixedHighestVector_E_zero q hq hq1 n r a b)
    (normalizedMixedHighestVector_E_zero q hq hq1 n s a b)
    (normalizedMixedHighestVector_K q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n r a b)
    (normalizedMixedHighestVector_K q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n s a b)
    ((normalizedMixedHighestVector_norm_one q hq n a b r hn).trans
      (normalizedMixedHighestVector_norm_one q hq n a b s hn).symm)


end AMSPhysical
#print axioms AMSPhysical.mixedCanonicalTransport
