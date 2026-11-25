import QuantumPhysicalCupVectors
import QuantumCupRankReduction

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

theorem physicalQuantumCupCoefficientEquiv_literal (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (l m h c : ℕ)
    (v : physicalQuantumCupSpan q n l m h c) :
    (physicalQuantumCupCoefficientEquiv q hq n hn l m h c v).val=occupationTripleCoefficients n l (m+h) c v.val := by
  have hMaps : (quantumCupSpan q n l m h c).subtype.comp
      (physicalQuantumCupCoefficientEquiv q hq n hn l m h c).toLinearMap=
      (occupationTripleCoefficients n l (m+h) c).comp (physicalQuantumCupSpan q n l m h c).subtype := by
    apply (physicalQuantumCupBasis q hq n hn l m h c).ext
    intro r
    change (physicalQuantumCupCoefficientEquiv q hq n hn l m h c (physicalQuantumCupBasis q hq n hn l m h c r)).val=_
    rw [physicalQuantumCupCoefficientEquiv_basis]
    change quantumCupMonomialAt q n l m h c r=
      occupationTripleCoefficients n l (m+h) c (physicalQuantumCupBasis q hq n hn l m h c r).val
    rw [show (physicalQuantumCupBasis q hq n hn l m h c r).val=physicalQuantumCupVector q n l m h c r from Module.Basis.span_apply _ r]
    exact (occupationTripleCoefficients_physicalCup q n l m h c r).symm
  exact DFunLike.congr_fun hMaps v

theorem physicalQuantumCupCoefficientEquiv_inverse_literal (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (l m h c : ℕ)
    (v : quantumCupSpan q n l m h c) :
    ((physicalQuantumCupCoefficientEquiv q hq n hn l m h c).symm v).val=occupationTripleSynthesis n l (m+h) c v.val := by
  have h0:=physicalQuantumCupCoefficientEquiv_literal q hq n hn l m h c
    ((physicalQuantumCupCoefficientEquiv q hq n hn l m h c).symm v)
  rw [LinearEquiv.apply_symm_apply] at h0
  have hs:=congrArg (occupationTripleSynthesis n l (m+h) c) h0
  rw [occupationTripleSynthesis_coefficients] at hs
  exact hs.symm

/-- The proved simultaneous cup-span bijection transported to literal finite
physical tensor spaces. This definition does not assert metric compatibility. -/
def physicalQuantumCupRankReduction (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (l m h c : ℕ) :
    physicalQuantumCupSpan q n l m h c ≃ₗ[ℝ] physicalQuantumCupSpan q 1 l m (h+n-1) c :=
  (physicalQuantumCupCoefficientEquiv q hq n hn l m h c).trans
    ((quantumCupRankReduction q hq n hn l m h c).trans
      (physicalQuantumCupCoefficientEquiv q hq 1 (by omega) l m (h+n-1) c).symm)

end AMSPhysical
