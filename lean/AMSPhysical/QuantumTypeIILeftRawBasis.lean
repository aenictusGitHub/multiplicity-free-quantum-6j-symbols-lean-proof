import QuantumTypeIILeftBasis
import Mathlib.LinearAlgebra.Basis.SMul

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

/-- Complete actual left basis before unit normalization. The rescaling is
by the proved strictly positive actual highest-vector norm. -/
def physicalTypeIILeftRawBasis (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) :
    Module.Basis (TypeIICommonIndex a b c d) ℝ
      (physicalTypeIIHighestSpace q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n a b c d) :=
  (physicalTypeIILeftBasis q hq hq1 n hn a b c d hbal).unitsSMul
    (fun r =>Units.mk0 (Real.sqrt (physicalTypeIILeftHighestNormSq q hq hq1 n hn a b c d hbal r))
      (ne_of_gt (Real.sqrt_pos.mpr (physicalTypeIILeftHighest_norm_pos q hq hq1 n hn a b c d hbal r))))

theorem physicalTypeIILeftRawBasis_apply (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (a b c d : ℕ) (hbal : a+b=c+d) (r : TypeIICommonIndex a b c d) :
    physicalTypeIILeftRawBasis q hq hq1 n hn a b c d hbal r=
      physicalTypeIILeftHighest q hq hq1 n hn a b c d hbal r := by
  have hs : Real.sqrt (physicalTypeIILeftHighestNormSq q hq hq1 n hn a b c d hbal r)≠0 :=
    ne_of_gt (Real.sqrt_pos.mpr (physicalTypeIILeftHighest_norm_pos q hq hq1 n hn a b c d hbal r))
  rw [physicalTypeIILeftRawBasis,Module.Basis.unitsSMul_apply,physicalTypeIILeftBasis_apply]
  simp only [Units.smul_def,Units.val_mk0,physicalTypeIILeftCoupling,smul_smul,mul_inv_cancel₀ hs,one_smul]

end AMSPhysical
#print axioms AMSPhysical.physicalTypeIILeftRawBasis
