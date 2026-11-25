import TypeIIStandardShiftedCreation
import RankTwoTypeIIRightChannel
import TypeIIStandardShiftedRightBasis
import QuantumTypeIICreationGram

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical

theorem standardHighestSecondDegreeEquiv_isometry (q:ℝ) (hq:q≠0) (hD:q-q⁻¹≠0)
    (a b b' c d:ℕ) (hb:b=b')
    (v w:standardTypeAHighestMultiplicity q hq hD a b c d):
    quantumTripleBilin q a b' c
      (standardHighestSecondDegreeEquiv q hq hD a b b' c d hb v).val
      (standardHighestSecondDegreeEquiv q hq hD a b b' c d hb w).val=
      quantumTripleBilin q a b c v.val w.val := by
  subst b'
  rfl

theorem standardTypeIIHighestRightCreation_gram_physical (q:ℝ) (hq:0<q) (hq1:q≠1) (a b c d:ℕ)
    (v w:standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) a b c d):
    quantumTripleBilin q a (b+1) (c+1)
      (standardTypeIIHighestRightCreation q hq hq1 a b c d v).val
      (standardTypeIIHighestRightCreation q hq hq1 a b c d w).val=
      physicalTypeIITripleBilin q 1 a (b+1) (c+1)
        (physicalTypeIIRightCreation q 1 a b c (rankTwoTypeIITripleEquiv a b c v.val))
        (physicalTypeIIRightCreation q 1 a b c (rankTwoTypeIITripleEquiv a b c w.val)) := by
  exact rankTwoTypeIIHighestEquiv_inverse_isometry q hq hq1 a (b+1) (c+1) d
    (physicalTypeIIHighestRightCreation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 a b c d
      (rankTwoTypeIIHighestEquiv q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) a b c d v))
    (physicalTypeIIHighestRightCreation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 a b c d
      (rankTwoTypeIIHighestEquiv q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) a b c d w))

theorem typeIIStandardShiftedRightHighest_creation_gram (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d)
    (v:standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (a+h) (b+h) c d)
    (t:QuantumCupIndex a c b):
    quantumTripleBilin q (a+h) (b+1+h) (c+1)
      (standardTypeIIShiftedRightCreation q hq hq1 h a b c d v).val
      (standardTypeIIShiftedRightCreation q hq hq1 h a b c d
        (typeIIStandardShiftedRightHighest q hq hq1 h a b c d hbal t)).val=
      mixedCreationSpectralScalar q 1 (b+h) c (c-t.val.val)*
        quantumTripleBilin q (a+h) (b+h) c v.val
          (typeIIStandardShiftedRightHighest q hq hq1 h a b c d hbal t).val := by
  unfold standardTypeIIShiftedRightCreation
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [standardHighestSecondDegreeEquiv_isometry,standardTypeIIHighestRightCreation_gram_physical q hq hq1]
  dsimp only [typeIIStandardShiftedRightHighest]
  rw [physicalTypeIIRightCreation_gram_channel q hq hq1 1 (by omega) (a+h) (b+h) c
    (typeIIShiftedRightCupIndex h a b c t) _ _
      (rankTwoTypeIITripleEquiv_shiftedRight_channel q hq hq1 h a b c t),
    rankTwoTypeIITripleEquiv_isometry q hq hq1]
  rfl

end AMSPhysical
#print axioms AMSPhysical.typeIIStandardShiftedRightHighest_creation_gram
