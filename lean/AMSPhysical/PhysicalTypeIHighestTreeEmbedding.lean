import CompactHighestFullEmbedding
import QuantumSymmetricHighestRealization
import QuantumTypeATripleCompact
import QuantumTypeAHighestSpace

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

abbrev physicalTypeIHighestSpace (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (n a b c d : ℕ) :=
  typeAHighestSpace (V:=quantumOccupationTripleSpace n a b c) q n
    (typeAMixedTriple q hq hD n a b c) (mixedHighestDynkin n d 0)

def physicalTypeIUnitHighestRealization (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n a b c d : ℕ)
    (v : physicalTypeIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d)
    (hvn : physicalTripleBilin q n a b c v.val v.val=1) :
    CompactHighestRealization q n (quantumOccupationTripleSpace n a b c) (mixedHighestDynkin n d 0) where
  action := typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c
  pairing := physicalTripleBilin q n a b c
  highest := v.val
  compact := typeAMixedTriple_compact q hq hq1 n a b c
  symmetric := physicalTripleBilin_symm q n a b c
  definite := physicalTripleBilin_definite q hq n a b c
  highestE := ((mem_typeAHighestSpace q n _ _ v.val).mp v.property).1
  highestK := ((mem_typeAHighestSpace q n _ _ v.val).mp v.property).2
  highestNorm := hvn

def physicalTypeIUnitHighestTreeMap (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n a b c d : ℕ)
    (v : physicalTypeIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d)
    (hvn : physicalTripleBilin q n a b c v.val v.val=1) :
    quantumOccupationSpace ℝ (Fin (n+1)) d →ₗ[ℝ] quantumOccupationTripleSpace n a b c :=
  (symmetricHighestRealization q hq hq1 n d).fullEmbedding (ne_of_gt hq)
    (symmetricHighestRealization_channel_top q hq hq1 n d)
    (physicalTypeIUnitHighestRealization q hq hq1 n a b c d v hvn)

theorem physicalTypeIUnitHighestTreeMap_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n a b c d : ℕ)
    (v : physicalTypeIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d)
    (hvn : physicalTripleBilin q n a b c v.val v.val=1) :
    physicalTypeIUnitHighestTreeMap q hq hq1 n a b c d v hvn
      (quantumOccupationBasis (K:=ℝ) d (highestOccupation n d))=v.val :=
  CompactHighestRealization.fullEmbedding_highest (ne_of_gt hq)
    (symmetricHighestRealization q hq hq1 n d) (symmetricHighestRealization_channel_top q hq hq1 n d)
    (physicalTypeIUnitHighestRealization q hq hq1 n a b c d v hvn)

theorem physicalTypeIUnitHighestTreeMap_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n a b c d : ℕ)
    (v : physicalTypeIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d)
    (hvn : physicalTripleBilin q n a b c v.val v.val=1) (z : UqTypeA q n)
    (x : quantumOccupationSpace ℝ (Fin (n+1)) d) :
    physicalTypeIUnitHighestTreeMap q hq hq1 n a b c d v hvn
      (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n d z x) =
      typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c z
        (physicalTypeIUnitHighestTreeMap q hq hq1 n a b c d v hvn x) :=
  CompactHighestRealization.fullEmbedding_intertwines (ne_of_gt hq)
    (symmetricHighestRealization q hq hq1 n d) (symmetricHighestRealization_channel_top q hq hq1 n d)
    (physicalTypeIUnitHighestRealization q hq hq1 n a b c d v hvn) z x

theorem physicalTypeIUnitHighestTreeMap_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n a b c d : ℕ)
    (v : physicalTypeIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d)
    (hvn : physicalTripleBilin q n a b c v.val v.val=1)
    (x y : quantumOccupationSpace ℝ (Fin (n+1)) d) :
    physicalTripleBilin q n a b c (physicalTypeIUnitHighestTreeMap q hq hq1 n a b c d v hvn x)
      (physicalTypeIUnitHighestTreeMap q hq hq1 n a b c d v hvn y) = occupationCompactBilin q n d x y :=
  CompactHighestRealization.fullEmbedding_isometry (ne_of_gt hq)
    (symmetricHighestRealization q hq hq1 n d) (symmetricHighestRealization_channel_top q hq hq1 n d)
    (physicalTypeIUnitHighestRealization q hq hq1 n a b c d v hvn) x y

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIUnitHighestTreeMap_isometry
