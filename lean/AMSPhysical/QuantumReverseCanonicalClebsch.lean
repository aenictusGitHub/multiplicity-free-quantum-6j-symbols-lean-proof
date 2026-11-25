import QuantumMixedHighestRealizations

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 180000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def reverseMixedCanonicalTransport (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (a b r : ℕ) :
    normalizedMixedChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n 0 a b ≃ₗ[ℝ]
      normalizedReverseMixedChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n r a b := by
  let V := quantumOccupationSpace ℝ (Fin (n+1)) (0+a) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (0+b)
  let W := quantumOccupationSpace ℝ (Fin (n+1)) (r+b) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (r+a)
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  exact CompactHighestRealization.transport (V:=V) (W:=W) (ne_of_gt hq)
    (mixedHighestRealization q hq hq1 n hn 0 a b) (reverseMixedHighestRealization q hq hq1 n hn r a b)

theorem reverseMixedCanonicalTransport_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b r : ℕ)
    (x y : normalizedMixedChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n 0 a b) :
    mixedTensorBilin q n (0+a) (0+b) x.val y.val=
      reverseMixedTensorBilin q n (r+b) (r+a) (reverseMixedCanonicalTransport q hq hq1 n hn a b r x).val
        (reverseMixedCanonicalTransport q hq hq1 n hn a b r y).val := by
  exact CompactHighestRealization.transport_isometry (ne_of_gt hq)
    (mixedHighestRealization q hq hq1 n hn 0 a b) (reverseMixedHighestRealization q hq hq1 n hn r a b) x y

theorem reverseMixedCanonicalTransport_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b r : ℕ) (z : UqTypeA q n)
    (x : normalizedMixedChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n 0 a b) :
    (reverseMixedCanonicalTransport q hq hq1 n hn a b r
      ⟨typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (0+a) (0+b) z x.val,
        algebraCyclicSpan_invariant _ _ z x.val x.property⟩).val=
      typeAReverseMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (r+b) (r+a) z
        (reverseMixedCanonicalTransport q hq hq1 n hn a b r x).val := by
  exact CompactHighestRealization.transport_intertwines (ne_of_gt hq)
    (mixedHighestRealization q hq hq1 n hn 0 a b) (reverseMixedHighestRealization q hq hq1 n hn r a b) z x

/-- Opposite/symmetric Clebsch embeddings use the SAME fixed physical
highest carrier as the forward-order embeddings. -/
def canonicalReverseMixedClebsch (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (a b r : ℕ) :
    normalizedMixedChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n 0 a b →ₗ[ℝ]
      (quantumOccupationSpace ℝ (Fin (n+1)) (r+b) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (r+a)) :=
  (normalizedReverseMixedChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n r a b).subtype.comp
    (reverseMixedCanonicalTransport q hq hq1 n hn a b r).toLinearMap

theorem canonicalReverseMixedClebsch_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (a b r : ℕ)
    (x y : normalizedMixedChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n 0 a b) :
    reverseMixedTensorBilin q n (r+b) (r+a) (canonicalReverseMixedClebsch q hq hq1 n hn a b r x)
      (canonicalReverseMixedClebsch q hq hq1 n hn a b r y)=mixedTensorBilin q n (0+a) (0+b) x.val y.val :=
  (reverseMixedCanonicalTransport_isometry q hq hq1 n hn a b r x y).symm

theorem canonicalReverseMixedClebsch_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n) (a b r : ℕ)
    (z : UqTypeA q n)
    (x : normalizedMixedChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n 0 a b) :
    canonicalReverseMixedClebsch q hq hq1 n hn a b r
      ⟨typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (0+a) (0+b) z x.val,
        algebraCyclicSpan_invariant _ _ z x.val x.property⟩=
      typeAReverseMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (r+b) (r+a) z
        (canonicalReverseMixedClebsch q hq hq1 n hn a b r x) :=
  reverseMixedCanonicalTransport_intertwines q hq hq1 n hn a b r z x

end AMSPhysical
#print axioms AMSPhysical.canonicalReverseMixedClebsch_intertwines
