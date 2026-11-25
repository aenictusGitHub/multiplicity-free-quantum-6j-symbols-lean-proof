import QuantumMixedCanonicalTransport
import CyclicSpanScale
import QuantumMixedIrreducible

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 4200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- One fixed highest-weight carrier is used for every tensor realization. -/
def canonicalMixedClebsch (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (a b r : ℕ) :
    normalizedMixedChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n 0 a b →ₗ[ℝ]
      (quantumOccupationSpace ℝ (Fin (n+1)) (r+a) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (r+b)) :=
  (normalizedMixedChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n r a b).subtype.comp
    (mixedCanonicalTransport q hq hq1 n hn a b 0 r).toLinearMap

theorem canonicalMixedClebsch_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (a b r : ℕ)
    (x y : normalizedMixedChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n 0 a b) :
    mixedTensorBilin q n (r+a) (r+b) (canonicalMixedClebsch q hq hq1 n hn a b r x)
      (canonicalMixedClebsch q hq hq1 n hn a b r y)=
      mixedTensorBilin q n (0+a) (0+b) x.val y.val := by
  exact (mixedCanonicalTransport_isometry q hq hq1 n hn a b 0 r x y).symm

/-- Model-independent physical Clebsch embeddings intertwine the entire
quantum algebra, for all ranks, all symmetric degrees and every mixed channel. -/
theorem canonicalMixedClebsch_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (a b r : ℕ)
    (z : UqTypeA q n)
    (x : normalizedMixedChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n 0 a b) :
    canonicalMixedClebsch q hq hq1 n hn a b r
      ⟨typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (0+a) (0+b) z x.val,
        algebraCyclicSpan_invariant _ _ z x.val x.property⟩=
      typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (r+a) (r+b) z
        (canonicalMixedClebsch q hq hq1 n hn a b r x) :=
  mixedCanonicalTransport_intertwines q hq hq1 n hn a b 0 r z x

/-- Normalization does not change the actual irreducible orbit submodule. -/
theorem normalizedMixedChannel_eq (q : ℝ) (hq : 0<q) (hD : q-q⁻¹≠0) (n r a b : ℕ) :
    normalizedMixedChannel q (ne_of_gt hq) hD n r a b=mixedChannelSubmodule q (ne_of_gt hq) hD n r a b := by
  unfold normalizedMixedChannel normalizedMixedHighestVector mixedChannelSubmodule
  apply algebraCyclicSpan_smul
  exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (mixedCouplingNormClosed_pos q hq n a b r)))

end AMSPhysical
#print axioms AMSPhysical.canonicalMixedClebsch_intertwines
