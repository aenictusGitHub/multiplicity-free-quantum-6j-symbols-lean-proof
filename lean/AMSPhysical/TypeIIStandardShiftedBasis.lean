import StandardFixedHighestBasis
import TypeIIShiftedPathEquivalence
import Mathlib.LinearAlgebra.Basis.SMul

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

def typeIIStandardShiftedLeftHighest (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d):=
  standardFixedLeftHighest q hq hq1 (a+h) (b+h) c d
    (typeIIShiftedFixedLeftPath h a b c d hbal r)

def typeIIStandardShiftedLeftBasis (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d):=
  (standardFixedLeftHighestBasis q hq hq1 (a+h) (b+h) c d).reindex
    (typeIIShiftedLeftPathEquiv h a b c d hbal).symm

theorem typeIIStandardShiftedLeftBasis_apply (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d):
    typeIIStandardShiftedLeftBasis q hq hq1 h a b c d hbal r=
      typeIIStandardShiftedLeftHighest q hq hq1 h a b c d hbal r := by
  simp only [typeIIStandardShiftedLeftBasis,Module.Basis.reindex_apply,Equiv.symm_symm,
    standardFixedLeftHighestBasis_apply]
  rfl

theorem typeIIStandardShiftedLeftHighest_pair (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (r s:TypeIICommonIndex a b c d):
    quantumTripleBilin q (a+h) (b+h) c
      (typeIIStandardShiftedLeftHighest q hq hq1 h a b c d hbal r).val
      (typeIIStandardShiftedLeftHighest q hq hq1 h a b c d hbal s).val=if r=s then 1 else 0 := by
  classical
  unfold typeIIStandardShiftedLeftHighest
  rw [standardFixedLeftHighest_pair]
  change (if (typeIIShiftedLeftPathEquiv h a b c d hbal r)=
    (typeIIShiftedLeftPathEquiv h a b c d hbal s) then 1 else 0)=_
  simp only [(typeIIShiftedLeftPathEquiv h a b c d hbal).injective.eq_iff]

def typeIIStandardShiftedSignedBasis (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d):=
  (typeIIStandardShiftedLeftBasis q hq hq1 h a b c d hbal).unitsSMul
    (fun r:TypeIICommonIndex a b c d=>(-1:ℝˣ)^r.val)

theorem typeIIStandardShiftedSignedBasis_apply (q:ℝ) (hq:0<q) (hq1:q≠1)
    (h a b c d:ℕ) (hbal:a+b=c+d) (r:TypeIICommonIndex a b c d):
    typeIIStandardShiftedSignedBasis q hq hq1 h a b c d hbal r=
      ((-1:ℝ)^r.val) • typeIIStandardShiftedLeftHighest q hq hq1 h a b c d hbal r := by
  simp only [typeIIStandardShiftedSignedBasis,Module.Basis.unitsSMul_apply,Units.smul_def,
    Units.val_pow_eq_pow_val,Units.val_neg,Units.val_one,typeIIStandardShiftedLeftBasis_apply]

end AMSPhysical
#print axioms AMSPhysical.typeIIStandardShiftedSignedBasis
