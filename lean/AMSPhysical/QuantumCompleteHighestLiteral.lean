import QuantumCompleteHighestOperators

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

theorem completeHighestCoefficientEquiv_inverse_literal (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1)
    (v : quantumCupSpan q n l m h c) :
    ((completeHighestCoefficientEquiv q hq hq1 n hn l m h c hadm hRank).symm v).val=
      occupationTripleSynthesis n l (m+h) c v.val := by
  have h0:=completeHighestCoefficientEquiv_literal q hq hq1 n hn l m h c hadm hRank
    ((completeHighestCoefficientEquiv q hq hq1 n hn l m h c hadm hRank).symm v)
  rw [LinearEquiv.apply_symm_apply] at h0
  have hs:=congrArg (occupationTripleSynthesis n l (m+h) c) h0
  rw [occupationTripleSynthesis_coefficients] at hs
  exact hs.symm

theorem completeHighestLeftAction_literal (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1)
    (v : physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c) :
    occupationTripleCoefficients n l (m+h) c
        (completeHighestLeftAction q hq hq1 n hn l m h c hadm hRank v).val=
      tripleLeftCreation q n (tripleLeftAnnihilation q n (occupationTripleCoefficients n l (m+h) c v.val)) := by
  rw [← completeHighestCoefficientEquiv_literal q hq hq1 n hn l m h c hadm hRank]
  unfold completeHighestLeftAction
  simp only [LinearEquiv.conj_apply,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
  change tripleLeftCreation q n (tripleLeftAnnihilation q n
      (completeHighestCoefficientEquiv q hq hq1 n hn l m h c hadm hRank v).val)=_
  rw [completeHighestCoefficientEquiv_literal]

theorem completeHighestRightAction_literal (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1)
    (v : physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c) :
    occupationTripleCoefficients n l (m+h) c
        (completeHighestRightAction q hq hq1 n hn l m h c hadm hRank v).val=
      tripleRightCreation q n (tripleRightAnnihilation q n (occupationTripleCoefficients n l (m+h) c v.val)) := by
  rw [← completeHighestCoefficientEquiv_literal q hq hq1 n hn l m h c hadm hRank]
  unfold completeHighestRightAction
  simp only [LinearEquiv.conj_apply,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
  change tripleRightCreation q n (tripleRightAnnihilation q n
      (completeHighestCoefficientEquiv q hq hq1 n hn l m h c hadm hRank v).val)=_
  rw [completeHighestCoefficientEquiv_literal]

theorem completeHighestCoefficientEquiv_metric (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1)
    (v w : physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c) :
    quantumCupPhysicalBilin q n l m h c
      (completeHighestCoefficientEquiv q hq hq1 n hn l m h c hadm hRank v)
      (completeHighestCoefficientEquiv q hq hq1 n hn l m h c hadm hRank w)=
      physicalTripleBilin q n l (m+h) c v.val w.val := by
  change physicalTripleBilin q n l (m+h) c
      (occupationTripleSynthesis n l (m+h) c (completeHighestCoefficientEquiv q hq hq1 n hn l m h c hadm hRank v).val)
      (occupationTripleSynthesis n l (m+h) c (completeHighestCoefficientEquiv q hq hq1 n hn l m h c hadm hRank w).val)=_
  rw [completeHighestCoefficientEquiv_literal,completeHighestCoefficientEquiv_literal,
    occupationTripleSynthesis_coefficients,occupationTripleSynthesis_coefficients]

end AMSPhysical
#print axioms AMSPhysical.completeHighestLeftAction_literal
#print axioms AMSPhysical.completeHighestRightAction_literal
