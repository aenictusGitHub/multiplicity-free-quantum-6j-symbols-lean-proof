import TypeIIStandardShiftedBasis
import BilinearBasisEquiv

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical

theorem typeIIStandardShiftedSignedBasis_pair (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (r s:TypeIICommonIndex a b c d):
    quantumTripleBilin q (a+h) (b+h) c
      (typeIIStandardShiftedSignedBasis q hq hq1 h a b c d hbal r).val
      (typeIIStandardShiftedSignedBasis q hq hq1 h a b c d hbal s).val=if r=s then 1 else 0 := by
  rw [typeIIStandardShiftedSignedBasis_apply,typeIIStandardShiftedSignedBasis_apply]
  simp only [Submodule.coe_smul_of_tower,map_smul,LinearMap.smul_apply,smul_eq_mul]
  rw [typeIIStandardShiftedLeftHighest_pair]
  split_ifs with he
  · subst s
    rw [mul_one,← mul_pow]
    norm_num
  · simp

/-- The independently constructed complete physical and shifted standard
orthonormal bases determine the candidate full-space isometry. Its operator
and right-channel compatibility are separate theorems. -/
def typeIIShiftedUnitEquiv (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d):
    physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a b c d ≃ₗ[ℝ]
      standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (a+h) (b+h) c d :=
  (physicalTypeIILeftBasis q hq hq1 (h+1) (by omega) a b c d hbal).equiv
    (typeIIStandardShiftedSignedBasis q hq hq1 h a b c d hbal) (Equiv.refl _)

theorem typeIIShiftedUnitEquiv_left (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d):
    typeIIShiftedUnitEquiv q hq hq1 h a b c d hbal
      (physicalTypeIILeftCoupling q hq hq1 (h+1) (by omega) a b c d hbal r)=
      ((-1:ℝ)^r.val) • typeIIStandardShiftedLeftHighest q hq hq1 h a b c d hbal r := by
  rw [typeIIShiftedUnitEquiv,← physicalTypeIILeftBasis_apply,Module.Basis.equiv_apply]
  exact typeIIStandardShiftedSignedBasis_apply q hq hq1 h a b c d hbal r

theorem typeIIShiftedUnitEquiv_isometry (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d)
    (v w:physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a b c d):
    quantumTripleBilin q (a+h) (b+h) c
      (typeIIShiftedUnitEquiv q hq hq1 h a b c d hbal v).val
      (typeIIShiftedUnitEquiv q hq hq1 h a b c d hbal w).val=
      physicalTypeIITripleBilin q (h+1) a b c v.val w.val := by
  let V:=physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a b c d
  let W:=standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (a+h) (b+h) c d
  letI:AddCommGroup V:=inferInstance
  letI:Module ℝ V:=inferInstance
  letI:AddCommGroup W:=inferInstance
  letI:Module ℝ W:=inferInstance
  apply bilinearBasisEquiv_isometry (V:=V) (W:=W)
    (restrictedBilinearPair (physicalTypeIITripleBilin q (h+1) a b c) V)
    (restrictedBilinearPair (quantumTripleBilin q (a+h) (b+h) c) W)
    (physicalTypeIILeftBasis q hq hq1 (h+1) (by omega) a b c d hbal)
    (typeIIStandardShiftedSignedBasis q hq hq1 h a b c d hbal)
  · intro r s
    rw [physicalTypeIILeftBasis_apply,physicalTypeIILeftBasis_apply]
    exact physicalTypeIILeftCoupling_pair q hq hq1 (h+1) (by omega) a b c d hbal r s
  · exact typeIIStandardShiftedSignedBasis_pair q hq hq1 h a b c d hbal

end AMSPhysical
#print axioms AMSPhysical.typeIIShiftedUnitEquiv_isometry
