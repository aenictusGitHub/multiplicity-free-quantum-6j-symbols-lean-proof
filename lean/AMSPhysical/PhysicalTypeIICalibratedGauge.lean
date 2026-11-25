import PhysicalTypeIIAMSFormula

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

/-- Explicit left vertex convention whose image is the positive standard
left coupling. This only changes the actual physical channel phase. -/
def physicalTypeIICalibratedLeft (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d):=
  ((-1:ℝ)^r.val) • physicalTypeIILeftCoupling q hq hq1 (h+1) (by omega) a b c d hbal r

/-- Actual right coupling fixed by the independently constructed shifted
standard channel gauge, without using an AMS factorial expression. -/
def physicalTypeIICalibratedRight (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (t:QuantumCupIndex a c b):=
  (typeIIShiftedUnitEquiv q hq hq1 h a b c d hbal).symm
    (typeIIStandardShiftedRightHighest q hq hq1 h a b c d hbal t)

theorem physicalTypeIICalibratedLeft_standard (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d):
    typeIIShiftedUnitEquiv q hq hq1 h a b c d hbal
      (physicalTypeIICalibratedLeft q hq hq1 h a b c d hbal r)=
      typeIIStandardShiftedLeftHighest q hq hq1 h a b c d hbal r := by
  rw [physicalTypeIICalibratedLeft,map_smul,typeIIShiftedUnitEquiv_left,smul_smul,
    AMSGeneral.sign_square,one_smul]

theorem physicalTypeIICalibratedRight_standard (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (t:QuantumCupIndex a c b):
    typeIIShiftedUnitEquiv q hq hq1 h a b c d hbal
      (physicalTypeIICalibratedRight q hq hq1 h a b c d hbal t)=
      typeIIStandardShiftedRightHighest q hq hq1 h a b c d hbal t :=
  LinearEquiv.apply_symm_apply _ _

theorem physicalTypeIICalibratedRight_phase (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (t:QuantumCupIndex a c b):
    ∃ e:ℝ,(e=1 ∨ e= -1) ∧ physicalTypeIICalibratedRight q hq hq1 h a b c d hbal t=
      e • physicalTypeIIRightCoupling q hq hq1 (h+1) (by omega) a b c d hbal t := by
  obtain ⟨e,he,hv⟩:=typeIIShiftedUnitEquiv_right q hq hq1 h a b c d hbal t
  refine ⟨e,he,?_⟩
  apply (typeIIShiftedUnitEquiv q hq hq1 h a b c d hbal).injective
  rw [physicalTypeIICalibratedRight_standard,map_smul,hv,smul_smul]
  rcases he with rfl|rfl <;> simp

theorem physicalTypeIICalibratedLeft_mem (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d):
    (physicalTypeIICalibratedLeft q hq hq1 h a b c d hbal r).val∈
      physicalTypeIILeftChannel q hq hq1 (h+1) (by omega) a b c d r :=
  Submodule.smul_mem _ _ (physicalTypeIILeftCoupling_mem q hq hq1 (h+1) (by omega) a b c d hbal r)

theorem physicalTypeIICalibratedRight_mem (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (t:QuantumCupIndex a c b):
    (physicalTypeIICalibratedRight q hq hq1 h a b c d hbal t).val∈
      physicalTypeIIRightChannel q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) (h+1) a b c t := by
  obtain ⟨e,_,he⟩:=physicalTypeIICalibratedRight_phase q hq hq1 h a b c d hbal t
  rw [he]
  exact Submodule.smul_mem _ _ (physicalTypeIIRightCoupling_mem q hq hq1 (h+1) (by omega) a b c d hbal t)

theorem physicalTypeIICalibratedLeft_unit (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d):
    physicalTypeIITripleBilin q (h+1) a b c
      (physicalTypeIICalibratedLeft q hq hq1 h a b c d hbal r).val
      (physicalTypeIICalibratedLeft q hq hq1 h a b c d hbal r).val=1 := by
  rw [← typeIIShiftedUnitEquiv_isometry q hq hq1 h a b c d hbal,
    physicalTypeIICalibratedLeft_standard,typeIIStandardShiftedLeftHighest_pair,if_pos rfl]

theorem physicalTypeIICalibratedRight_unit (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (t:QuantumCupIndex a c b):
    physicalTypeIITripleBilin q (h+1) a b c
      (physicalTypeIICalibratedRight q hq hq1 h a b c d hbal t).val
      (physicalTypeIICalibratedRight q hq hq1 h a b c d hbal t).val=1 := by
  rw [← typeIIShiftedUnitEquiv_isometry q hq hq1 h a b c d hbal,
    physicalTypeIICalibratedRight_standard,typeIIStandardShiftedRightHighest_pair,if_pos rfl]

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIICalibratedRight_mem
