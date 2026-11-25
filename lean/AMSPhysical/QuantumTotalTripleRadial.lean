import QuantumCompleteHighestLiteral
import QuantumFiniteTripleRadial

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

def physicalTripleLeftRadialTotal (q : ℝ) (n l m c : ℕ) : Module.End ℝ (quantumOccupationTripleSpace n l m c) :=
  (occupationTripleSynthesis n l m c).comp
    (((tripleLeftCreation q n).comp (tripleLeftAnnihilation q n)).comp (occupationTripleCoefficients n l m c))

def physicalTripleRightRadialTotal (q : ℝ) (n l m c : ℕ) : Module.End ℝ (quantumOccupationTripleSpace n l m c) :=
  (occupationTripleSynthesis n l m c).comp
    (((tripleRightCreation q n).comp (tripleRightAnnihilation q n)).comp (occupationTripleCoefficients n l m c))

theorem physicalTripleLeftRadialTotal_positive (q : ℝ) (n l m c : ℕ) :
    physicalTripleLeftRadialTotal q n (l+1) (m+1) c=finiteTripleLeftRadial q n l m c := by
  apply LinearMap.ext
  intro v
  have hs:=congrArg (occupationTripleSynthesis n (l+1) (m+1) c) (occupationTripleCoefficients_leftRadial q n l m c v)
  rw [occupationTripleSynthesis_coefficients] at hs
  exact hs.symm

theorem physicalTripleRightRadialTotal_positive (q : ℝ) (n l m c : ℕ) :
    physicalTripleRightRadialTotal q n l (m+1) (c+1)=finiteTripleRightRadial q n l m c := by
  apply LinearMap.ext
  intro v
  have hs:=congrArg (occupationTripleSynthesis n l (m+1) (c+1)) (occupationTripleCoefficients_rightRadial q n l m c v)
  rw [occupationTripleSynthesis_coefficients] at hs
  exact hs.symm

theorem completeHighestLeftAction_ambient (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1)
    (v : physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c) :
    (completeHighestLeftAction q hq hq1 n hn l m h c hadm hRank v).val=
      physicalTripleLeftRadialTotal q n l (m+h) c v.val := by
  have hs:=congrArg (occupationTripleSynthesis n l (m+h) c)
    (completeHighestLeftAction_literal q hq hq1 n hn l m h c hadm hRank v)
  rw [occupationTripleSynthesis_coefficients] at hs
  exact hs

theorem completeHighestRightAction_ambient (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1)
    (v : physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c) :
    (completeHighestRightAction q hq hq1 n hn l m h c hadm hRank v).val=
      physicalTripleRightRadialTotal q n l (m+h) c v.val := by
  have hs:=congrArg (occupationTripleSynthesis n l (m+h) c)
    (completeHighestRightAction_literal q hq hq1 n hn l m h c hadm hRank v)
  rw [occupationTripleSynthesis_coefficients] at hs
  exact hs

end AMSPhysical
#print axioms AMSPhysical.completeHighestLeftAction_ambient
#print axioms AMSPhysical.completeHighestRightAction_ambient
