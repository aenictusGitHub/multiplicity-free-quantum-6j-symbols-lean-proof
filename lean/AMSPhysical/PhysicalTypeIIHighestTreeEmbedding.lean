import CompactHighestFullEmbedding
import QuantumSymmetricHighestRealization
import QuantumTypeIICompact
import QuantumTypeAHighestSpace

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

def physicalTypeIIUnitHighestRealization (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ)
    (v : physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d)
    (hvn : physicalTypeIITripleBilin q n a b c v.val v.val=1) :
    CompactHighestRealization q n (quantumOccupationTripleSpace n a b c) (mixedHighestDynkin n d 0) where
  action := typeATypeIITriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c
  pairing := physicalTypeIITripleBilin q n a b c
  highest := v.val
  compact := typeATypeIITriple_compact q hq hq1 n a b c
  symmetric := physicalTypeIITripleBilin_symm q n a b c
  definite := physicalTypeIITripleBilin_definite q hq hq1 n hn a b c
  highestE := ((mem_typeAHighestSpace q n _ _ v.val).mp v.property).1
  highestK := ((mem_typeAHighestSpace q n _ _ v.val).mp v.property).2
  highestNorm := hvn

def physicalTypeIIUnitHighestTreeMap (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ)
    (v : physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d)
    (hvn : physicalTypeIITripleBilin q n a b c v.val v.val=1) :
    quantumOccupationSpace ℝ (Fin (n+1)) d →ₗ[ℝ] quantumOccupationTripleSpace n a b c :=
  (symmetricHighestRealization q hq hq1 n d).fullEmbedding (ne_of_gt hq)
    (symmetricHighestRealization_channel_top q hq hq1 n d)
    (physicalTypeIIUnitHighestRealization q hq hq1 n hn a b c d v hvn)

theorem physicalTypeIIUnitHighestTreeMap_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ)
    (v : physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d)
    (hvn : physicalTypeIITripleBilin q n a b c v.val v.val=1) :
    physicalTypeIIUnitHighestTreeMap q hq hq1 n hn a b c d v hvn
      (quantumOccupationBasis (K:=ℝ) d (highestOccupation n d))=v.val :=
  CompactHighestRealization.fullEmbedding_highest (ne_of_gt hq)
    (symmetricHighestRealization q hq hq1 n d) (symmetricHighestRealization_channel_top q hq hq1 n d)
    (physicalTypeIIUnitHighestRealization q hq hq1 n hn a b c d v hvn)

theorem physicalTypeIIUnitHighestTreeMap_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ)
    (v : physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d)
    (hvn : physicalTypeIITripleBilin q n a b c v.val v.val=1) (z : UqTypeA q n)
    (x : quantumOccupationSpace ℝ (Fin (n+1)) d) :
    physicalTypeIIUnitHighestTreeMap q hq hq1 n hn a b c d v hvn
      (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n d z x) =
    typeATypeIITriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c z
      (physicalTypeIIUnitHighestTreeMap q hq hq1 n hn a b c d v hvn x) :=
  CompactHighestRealization.fullEmbedding_intertwines (ne_of_gt hq)
    (symmetricHighestRealization q hq hq1 n d) (symmetricHighestRealization_channel_top q hq hq1 n d)
    (physicalTypeIIUnitHighestRealization q hq hq1 n hn a b c d v hvn) z x

theorem physicalTypeIIUnitHighestTreeMap_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b c d : ℕ)
    (v : physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d)
    (hvn : physicalTypeIITripleBilin q n a b c v.val v.val=1)
    (x y : quantumOccupationSpace ℝ (Fin (n+1)) d) :
    physicalTypeIITripleBilin q n a b c (physicalTypeIIUnitHighestTreeMap q hq hq1 n hn a b c d v hvn x)
      (physicalTypeIIUnitHighestTreeMap q hq hq1 n hn a b c d v hvn y) = occupationCompactBilin q n d x y :=
  CompactHighestRealization.fullEmbedding_isometry (ne_of_gt hq)
    (symmetricHighestRealization q hq hq1 n d) (symmetricHighestRealization_channel_top q hq hq1 n d)
    (physicalTypeIIUnitHighestRealization q hq hq1 n hn a b c d v hvn) x y

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIIUnitHighestTreeMap_intertwines
