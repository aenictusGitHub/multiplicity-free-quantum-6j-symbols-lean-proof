import QuantumTypeIICompact
import QuantumTypeIILeftUnit
import CompactHighestIntertwinerMetric

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
noncomputable section
namespace AMSPhysical

/-- Actual full output-irrep metric identity for each Type-II left tree;
its scale is exactly the independently defined raw highest-vector norm. -/
theorem physicalTypeIILeftTreeMap_metric (q : ℝ) (hq:0<q) (hq1:q≠1)
    (n:ℕ) (hn:0<n) (a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d)
    (v w:quantumOccupationSpace ℝ (Fin (n+1)) d) :
    physicalTypeIITripleBilin q n a b c
      (physicalTypeIILeftTreeMap q hq hq1 n hn a b c d hbal r v)
      (physicalTypeIILeftTreeMap q hq hq1 n hn a b c d hbal r w)=
      physicalTypeIILeftHighestNormSq q hq hq1 n hn a b c d hbal r*occupationCompactBilin q n d v w := by
  let V:=quantumOccupationSpace ℝ (Fin (n+1)) d
  let W:=quantumOccupationTripleSpace n a b c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  exact compactHighestIntertwiner_metric (V:=V) (W:=W) q (ne_of_gt hq) n (mixedHighestDynkin n d 0)
    (symmetricHighestRealization q hq hq1 n d) (symmetricHighestRealization_channel_top q hq hq1 n d)
    (typeATypeIITriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c)
    (physicalTypeIITripleBilin q n a b c) (typeATypeIITriple_compact q hq hq1 n a b c)
    (physicalTypeIITripleBilin_symm q n a b c)
    (physicalTypeIILeftTreeMap q hq hq1 n hn a b c d hbal r)
    (physicalTypeIILeftTreeMap_intertwines q hq hq1 n hn a b c d hbal r) v w

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIILeftTreeMap_metric
