import CompactHighestFullEmbedding
import QuantumSymmetricHighestRealization
import QuantumTypeATripleCompact
import QuantumCompleteHighestOperators
import QuantumPhysicalTripleInstances

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

def physicalTripleHighestRealization (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m h c : ℕ)
    (v : physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c)
    (hvn : physicalTripleBilin q n l (m+h) c v.val v.val=1) :
    CompactHighestRealization q n (quantumOccupationTripleSpace n l (m+h) c) (mixedHighestDynkin n (l+c-m+h) 0) where
  action := typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l (m+h) c
  pairing := physicalTripleBilin q n l (m+h) c
  highest := v.val
  compact := typeAMixedTriple_compact q hq hq1 n l (m+h) c
  symmetric := physicalTripleBilin_symm q n l (m+h) c
  definite := physicalTripleBilin_definite q hq n l (m+h) c
  highestE := ((mem_typeAHighestSpace q n _ _ v.val).mp v.property).1
  highestK := ((mem_typeAHighestSpace q n _ _ v.val).mp v.property).2
  highestNorm := hvn

/-- Every actual unit highest vector gives a constructed isometric
intertwiner from the entire output symmetric irrep into the physical triple. -/
def physicalHighestTreeEmbedding (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m h c : ℕ)
    (v : physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c)
    (hvn : physicalTripleBilin q n l (m+h) c v.val v.val=1) :
    quantumOccupationSpace ℝ (Fin (n+1)) (l+c-m+h) →ₗ[ℝ] quantumOccupationTripleSpace n l (m+h) c :=
  (symmetricHighestRealization q hq hq1 n (l+c-m+h)).fullEmbedding (ne_of_gt hq)
    (symmetricHighestRealization_channel_top q hq hq1 n (l+c-m+h))
    (physicalTripleHighestRealization q hq hq1 n l m h c v hvn)

theorem physicalHighestTreeEmbedding_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m h c : ℕ)
    (v : physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c)
    (hvn : physicalTripleBilin q n l (m+h) c v.val v.val=1)
    (x y : quantumOccupationSpace ℝ (Fin (n+1)) (l+c-m+h)) :
    physicalTripleBilin q n l (m+h) c (physicalHighestTreeEmbedding q hq hq1 n l m h c v hvn x)
      (physicalHighestTreeEmbedding q hq hq1 n l m h c v hvn y)=occupationCompactBilin q n (l+c-m+h) x y :=
  CompactHighestRealization.fullEmbedding_isometry (ne_of_gt hq) (symmetricHighestRealization q hq hq1 n (l+c-m+h))
    (symmetricHighestRealization_channel_top q hq hq1 n (l+c-m+h))
    (physicalTripleHighestRealization q hq hq1 n l m h c v hvn) x y

theorem physicalHighestTreeEmbedding_intertwines (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m h c : ℕ)
    (v : physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c)
    (hvn : physicalTripleBilin q n l (m+h) c v.val v.val=1)
    (z : UqTypeA q n) (x : quantumOccupationSpace ℝ (Fin (n+1)) (l+c-m+h)) :
    physicalHighestTreeEmbedding q hq hq1 n l m h c v hvn
      (typeAFiniteQuantumRepresentation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n (l+c-m+h) z x)=
      typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l (m+h) c z
        (physicalHighestTreeEmbedding q hq hq1 n l m h c v hvn x) :=
  CompactHighestRealization.fullEmbedding_intertwines (ne_of_gt hq) (symmetricHighestRealization q hq hq1 n (l+c-m+h))
    (symmetricHighestRealization_channel_top q hq hq1 n (l+c-m+h))
    (physicalTripleHighestRealization q hq hq1 n l m h c v hvn) z x

theorem physicalHighestTreeEmbedding_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m h c : ℕ)
    (v : physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c)
    (hvn : physicalTripleBilin q n l (m+h) c v.val v.val=1) :
    physicalHighestTreeEmbedding q hq hq1 n l m h c v hvn
      (quantumOccupationBasis (K:=ℝ) (l+c-m+h) (highestOccupation n (l+c-m+h)))=v.val :=
  CompactHighestRealization.fullEmbedding_highest (ne_of_gt hq) (symmetricHighestRealization q hq hq1 n (l+c-m+h))
    (symmetricHighestRealization_channel_top q hq hq1 n (l+c-m+h))
    (physicalTripleHighestRealization q hq hq1 n l m h c v hvn)

end AMSPhysical
#print axioms AMSPhysical.physicalHighestTreeEmbedding_isometry
#print axioms AMSPhysical.physicalHighestTreeEmbedding_intertwines
