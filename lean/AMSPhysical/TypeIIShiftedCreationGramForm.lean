import TypeIIShiftedCreationTransport
import TypeIIStandardShiftedCreationGram
import GramEigenvectorGauge

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

def typeIIShiftedCreationGramForm (q:ℝ) (hq:0<q) (hq1:q≠1) (h a b c d:ℕ):
    LinearMap.BilinForm ℝ
      (standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (a+h) (b+h) c d) :=
  (typeIICreationIsometryScalar q h a b d)^2 •
    (restrictedBilinearPair (quantumTripleBilin q (a+h) (b+1+h) (c+1))
      (standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
        (a+h) (b+1+h) (c+1) d)).compl₁₂
      (standardTypeIIShiftedRightCreation q hq hq1 h a b c d)
      (standardTypeIIShiftedRightCreation q hq hq1 h a b c d)

theorem typeIIShiftedCreationGramForm_apply (q:ℝ) (hq:0<q) (hq1:q≠1) (h a b c d:ℕ)
    (v w:standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (a+h) (b+h) c d):
    typeIIShiftedCreationGramForm q hq hq1 h a b c d v w=
      (typeIICreationIsometryScalar q h a b d)^2*quantumTripleBilin q (a+h) (b+1+h) (c+1)
        (standardTypeIIShiftedRightCreation q hq hq1 h a b c d v).val
        (standardTypeIIShiftedRightCreation q hq hq1 h a b c d w).val := rfl

theorem typeIIShiftedCreationGramForm_symm (q:ℝ) (hq:0<q) (hq1:q≠1) (h a b c d:ℕ)
    (v w:standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (a+h) (b+h) c d):
    typeIIShiftedCreationGramForm q hq hq1 h a b c d v w=
      typeIIShiftedCreationGramForm q hq hq1 h a b c d w v := by
  rw [typeIIShiftedCreationGramForm_apply,typeIIShiftedCreationGramForm_apply,
    quantumTripleBilin_symm q hq hq1]

theorem typeIIShiftedCreationGramForm_standardRight (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d)
    (v:standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (a+h) (b+h) c d)
    (t:QuantumCupIndex a c b):
    typeIIShiftedCreationGramForm q hq hq1 h a b c d v
      (typeIIStandardShiftedRightHighest q hq hq1 h a b c d hbal t)=
      mixedCreationSpectralScalar q (h+1) b c (c-t.val.val)*
        quantumTripleBilin q (a+h) (b+h) c v.val
          (typeIIStandardShiftedRightHighest q hq hq1 h a b c d hbal t).val := by
  rw [typeIIShiftedCreationGramForm_apply,typeIIStandardShiftedRightHighest_creation_gram,
    ← mul_assoc,typeIICreationIsometryScalar_spectral q hq]

theorem typeIIShiftedCreationGramForm_physicalRight (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d)
    (x:standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (a+h) (b+h) c d)
    (t:QuantumCupIndex a c b):
    typeIIShiftedCreationGramForm q hq hq1 h a b c d x
      (typeIIShiftedUnitEquiv q hq hq1 h a b c d hbal
        (physicalTypeIIRightCoupling q hq hq1 (h+1) (by omega) a b c d hbal t))=
      mixedCreationSpectralScalar q (h+1) b c (c-t.val.val)*
        quantumTripleBilin q (a+h) (b+h) c x.val
          (typeIIShiftedUnitEquiv q hq hq1 h a b c d hbal
            (physicalTypeIIRightCoupling q hq hq1 (h+1) (by omega) a b c d hbal t)).val := by
  let V:=physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a b c d
  let W:=standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (a+h) (b+h) c d
  let V':=physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a (b+1) (c+1) d
  let W':=standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (a+h) (b+1+h) (c+1) d
  letI:AddCommGroup V:=inferInstance
  letI:Module ℝ V:=inferInstance
  letI:AddCommGroup W:=inferInstance
  letI:Module ℝ W:=inferInstance
  letI:AddCommGroup V':=inferInstance
  letI:Module ℝ V':=inferInstance
  letI:AddCommGroup W':=inferInstance
  letI:Module ℝ W':=inferInstance
  let E:=typeIIShiftedUnitEquiv q hq hq1 h a b c d hbal
  let y:=E.symm x
  let v:=physicalTypeIIRightCoupling q hq hq1 (h+1) (by omega) a b c d hbal t
  have he:=scaledCreationGram_transport (V:=V) (W:=W) (V':=V') (W':=W')
    (restrictedBilinearPair (physicalTypeIITripleBilin q (h+1) a (b+1) (c+1)) V')
    (restrictedBilinearPair (quantumTripleBilin q (a+h) (b+1+h) (c+1)) W')
    E (typeIIShiftedUnitEquiv q hq hq1 h a (b+1) (c+1) d (by omega))
    (physicalTypeIIHighestRightCreation q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a b c d)
    (standardTypeIIShiftedRightCreation q hq hq1 h a b c d) (typeIICreationIsometryScalar q h a b d)
    (typeIIShiftedUnitEquiv_isometry q hq hq1 h a (b+1) (c+1) d (by omega))
    (typeIIShiftedUnitEquiv_creation q hq hq1 h a b c d hbal) y v
  change (typeIICreationIsometryScalar q h a b d)^2*quantumTripleBilin q (a+h) (b+1+h) (c+1)
      (standardTypeIIShiftedRightCreation q hq hq1 h a b c d (E y)).val
      (standardTypeIIShiftedRightCreation q hq hq1 h a b c d (E v)).val=
    physicalTypeIITripleBilin q (h+1) a (b+1) (c+1)
      (physicalTypeIIRightCreation q (h+1) a b c y.val)
      (physicalTypeIIRightCreation q (h+1) a b c v.val) at he
  rw [physicalTypeIIRightCreation_gram_channel q hq hq1 (h+1) (by omega) a b c t _ _
    (physicalTypeIIRightCoupling_mem q hq hq1 (h+1) (by omega) a b c d hbal t)] at he
  rw [← typeIIShiftedUnitEquiv_isometry q hq hq1 h a b c d hbal y v] at he
  simpa only [y,E,LinearEquiv.apply_symm_apply,typeIIRightIndex_val,typeIIShiftedCreationGramForm_apply] using he

end AMSPhysical
#print axioms AMSPhysical.typeIIShiftedCreationGramForm_physicalRight
