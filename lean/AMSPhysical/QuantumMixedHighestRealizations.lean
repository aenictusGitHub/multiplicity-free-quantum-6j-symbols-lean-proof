import CompactHighestRealization
import QuantumMixedCanonicalCore
import QuantumReverseNormalizedHighest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 180000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def mixedHighestRealization (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (r a b : ℕ) :
    CompactHighestRealization q n
      (quantumOccupationSpace ℝ (Fin (n+1)) (r+a) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (r+b))
      (mixedHighestDynkin n a b) where
  action := typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (r+a) (r+b)
  pairing := mixedTensorBilin q n (r+a) (r+b)
  highest := normalizedMixedHighestVector q n r a b
  compact := typeAMixedTensor_compact q hq hq1 n (r+a) (r+b)
  symmetric := mixedTensorBilin_symm q n (r+a) (r+b)
  definite := mixedTensorBilin_definite q hq n (r+a) (r+b)
  highestE := normalizedMixedHighestVector_E_zero q hq hq1 n r a b
  highestK := normalizedMixedHighestVector_K q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n r a b
  highestNorm := normalizedMixedHighestVector_norm_one q hq n a b r hn

def reverseMixedHighestRealization (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (r a b : ℕ) :
    CompactHighestRealization q n
      (quantumOccupationSpace ℝ (Fin (n+1)) (r+b) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (r+a))
      (mixedHighestDynkin n a b) where
  action := typeAReverseMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (r+b) (r+a)
  pairing := reverseMixedTensorBilin q n (r+b) (r+a)
  highest := normalizedReverseMixedHighest q n r a b
  compact := typeAReverseMixedTensor_compact q hq hq1 n (r+b) (r+a)
  symmetric := reverseMixedTensorBilin_symm q n (r+b) (r+a)
  definite := reverseMixedTensorBilin_definite q hq n (r+b) (r+a)
  highestE := normalizedReverseMixedHighest_E_zero q hq hq1 n r a b
  highestK := normalizedReverseMixedHighest_K q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n r a b
  highestNorm := normalizedReverseMixedHighest_norm_one q hq n hn r a b

end AMSPhysical
