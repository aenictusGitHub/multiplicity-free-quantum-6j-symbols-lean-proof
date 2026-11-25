import QuantumCupUnitaryRankReduction

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

/-- A literal finite physical-cup-space equivalence; the positive normalization
and both intermediate-operator intertwinings have already been derived. -/
def physicalQuantumCupUnitaryRankReduction (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m ≤ l+c) :
    physicalQuantumCupSpan q n l m h c ≃ₗ[ℝ] physicalQuantumCupSpan q 1 l m (h+n-1) c :=
  (physicalQuantumCupCoefficientEquiv q hq n hn l m h c).trans
    ((quantumCupUnitaryRankReduction q hq n hn l m h c hadm).trans
      (physicalQuantumCupCoefficientEquiv q hq 1 (by omega) l m (h+n-1) c).symm)

theorem physicalQuantumCupUnitaryRankReduction_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m ≤ l+c) (v w : physicalQuantumCupSpan q n l m h c) :
    physicalTripleBilin q 1 l (m+(h+n-1)) c
      (physicalQuantumCupUnitaryRankReduction q hq n hn l m h c hadm v).val
      (physicalQuantumCupUnitaryRankReduction q hq n hn l m h c hadm w).val=
      physicalTripleBilin q n l (m+h) c v.val w.val := by
  change physicalTripleBilin q 1 l (m+(h+n-1)) c
    ((physicalQuantumCupCoefficientEquiv q hq 1 (by omega) l m (h+n-1) c).symm
      (quantumCupUnitaryRankReduction q hq n hn l m h c hadm
        (physicalQuantumCupCoefficientEquiv q hq n hn l m h c v))).val
    ((physicalQuantumCupCoefficientEquiv q hq 1 (by omega) l m (h+n-1) c).symm
      (quantumCupUnitaryRankReduction q hq n hn l m h c hadm
        (physicalQuantumCupCoefficientEquiv q hq n hn l m h c w))).val=_
  rw [physicalQuantumCupCoefficientEquiv_inverse_literal,physicalQuantumCupCoefficientEquiv_inverse_literal]
  change quantumCupPhysicalBilin q 1 l m (h+n-1) c
    (quantumCupUnitaryRankReduction q hq n hn l m h c hadm (physicalQuantumCupCoefficientEquiv q hq n hn l m h c v))
    (quantumCupUnitaryRankReduction q hq n hn l m h c hadm (physicalQuantumCupCoefficientEquiv q hq n hn l m h c w))=_
  rw [quantumCupUnitaryRankReduction_isometry q hq hq1]
  change physicalTripleBilin q n l (m+h) c
    (occupationTripleSynthesis n l (m+h) c (physicalQuantumCupCoefficientEquiv q hq n hn l m h c v).val)
    (occupationTripleSynthesis n l (m+h) c (physicalQuantumCupCoefficientEquiv q hq n hn l m h c w).val)=_
  rw [physicalQuantumCupCoefficientEquiv_literal,physicalQuantumCupCoefficientEquiv_literal,
    occupationTripleSynthesis_coefficients,occupationTripleSynthesis_coefficients]

end AMSPhysical
#print axioms AMSPhysical.physicalQuantumCupUnitaryRankReduction_isometry
