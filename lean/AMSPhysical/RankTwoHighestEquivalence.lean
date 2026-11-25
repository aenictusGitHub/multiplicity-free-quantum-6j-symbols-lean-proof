import RankTwoMixedTripleEquivalence
import TypeAHighestSpaceEquivalence
import QuantumCompleteHighestOperators

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

abbrev standardTypeAHighestMultiplicity (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (l m c H : ℕ) :=
  typeAHighestSpace q 1 ((finiteTripleRepresentation q hq hD l m c).comp (rankTwoToSL2 q)) (mixedHighestDynkin 1 H 0)

def rankTwoHighestEquiv (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (l m c H : ℕ) :
    standardTypeAHighestMultiplicity q hq hD l m c H ≃ₗ[ℝ]
      typeAHighestSpace (V:=quantumOccupationTripleSpace 1 l m c) q 1
        (typeAMixedTriple q hq hD 1 l m c) (mixedHighestDynkin 1 H 0) := by
  let V := RealQuantumTripleSpace l m c
  let W := quantumOccupationTripleSpace 1 l m c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  exact typeAHighestSpaceEquiv (V:=V) (W:=W) q 1
    ((finiteTripleRepresentation q hq hD l m c).comp (rankTwoToSL2 q))
    (typeAMixedTriple q hq hD 1 l m c) (rankTwoMixedTripleEquiv l m c)
    (rankTwoMixedTripleEquiv_intertwines q hq hD l m c) (mixedHighestDynkin 1 H 0)

theorem rankTwoHighestEquiv_literal (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (l m c H : ℕ)
    (v : standardTypeAHighestMultiplicity q hq hD l m c H) :
    (rankTwoHighestEquiv q hq hD l m c H v).val=rankTwoMixedTripleEquiv l m c v.val := rfl

theorem rankTwoHighestEquiv_inverse_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m c H : ℕ)
    (v w : typeAHighestSpace (V:=quantumOccupationTripleSpace 1 l m c) q 1
      (typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 l m c) (mixedHighestDynkin 1 H 0)) :
    quantumTripleBilin q l m c
      ((rankTwoHighestEquiv q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m c H).symm v).val
      ((rankTwoHighestEquiv q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m c H).symm w).val=
      physicalTripleBilin q 1 l m c v.val w.val := by
  have hv:=congrArg Subtype.val ((rankTwoHighestEquiv q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m c H).apply_symm_apply v)
  have hw:=congrArg Subtype.val ((rankTwoHighestEquiv q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m c H).apply_symm_apply w)
  rw [rankTwoHighestEquiv_literal] at hv hw
  rw [← hv,← hw,rankTwoMixedTripleEquiv_isometry q hq hq1]

/-- The complete arbitrary-rank Type-I physical multiplicity space is
isometrically identified with the independently constructed standard sl2
highest space at the AMS-shifted external and total labels. -/
def fullPhysicalHighestToStandard (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) :
    physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c ≃ₗ[ℝ]
      standardTypeAHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
        l (m+(h+n-1)) c (l+c-m+(h+n-1)) :=
  (fullPhysicalHighestRankReduction q hq hq1 n hn l m h c hadm hRank).trans
    (rankTwoHighestEquiv q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      l (m+(h+n-1)) c (l+c-m+(h+n-1))).symm

theorem fullPhysicalHighestToStandard_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1)
    (v w : physicalQuantumHighestMultiplicity q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l m h c) :
    quantumTripleBilin q l (m+(h+n-1)) c
      (fullPhysicalHighestToStandard q hq hq1 n hn l m h c hadm hRank v).val
      (fullPhysicalHighestToStandard q hq hq1 n hn l m h c hadm hRank w).val=
      physicalTripleBilin q n l (m+h) c v.val w.val := by
  unfold fullPhysicalHighestToStandard
  simp only [LinearEquiv.trans_apply]
  rw [rankTwoHighestEquiv_inverse_isometry q hq hq1,fullPhysicalHighestRankReduction_isometry q hq hq1]

end AMSPhysical
#print axioms AMSPhysical.fullPhysicalHighestToStandard_isometry
