import RankTwoTypeIITripleEquivalence
import RankTwoHighestEquivalence
import TypeAHighestSpaceEquivalence
import QuantumCompleteHighestOperators

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

def rankTwoTypeIIHighestEquiv (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (l m c H : ℕ) :
    standardTypeAHighestMultiplicity q hq hD l m c H ≃ₗ[ℝ]
      typeAHighestSpace (V:=quantumOccupationTripleSpace 1 l m c) q 1
        (typeATypeIITriple q hq hD 1 l m c) (mixedHighestDynkin 1 H 0) := by
  let V := RealQuantumTripleSpace l m c
  let W := quantumOccupationTripleSpace 1 l m c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  exact typeAHighestSpaceEquiv (V:=V) (W:=W) q 1
    ((finiteTripleRepresentation q hq hD l m c).comp (rankTwoToSL2 q))
    (typeATypeIITriple q hq hD 1 l m c) (rankTwoTypeIITripleEquiv l m c)
    (rankTwoTypeIITripleEquiv_intertwines q hq hD l m c) (mixedHighestDynkin 1 H 0)

theorem rankTwoTypeIIHighestEquiv_literal (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (l m c H : ℕ)
    (v : standardTypeAHighestMultiplicity q hq hD l m c H) :
    (rankTwoTypeIIHighestEquiv q hq hD l m c H v).val=rankTwoTypeIITripleEquiv l m c v.val := rfl

theorem rankTwoTypeIIHighestEquiv_inverse_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m c H : ℕ)
    (v w : typeAHighestSpace (V:=quantumOccupationTripleSpace 1 l m c) q 1
      (typeATypeIITriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 l m c) (mixedHighestDynkin 1 H 0)) :
    quantumTripleBilin q l m c
      ((rankTwoTypeIIHighestEquiv q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m c H).symm v).val
      ((rankTwoTypeIIHighestEquiv q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m c H).symm w).val=
      physicalTypeIITripleBilin q 1 l m c v.val w.val := by
  have hv:=congrArg Subtype.val ((rankTwoTypeIIHighestEquiv q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m c H).apply_symm_apply v)
  have hw:=congrArg Subtype.val ((rankTwoTypeIIHighestEquiv q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) l m c H).apply_symm_apply w)
  rw [rankTwoTypeIIHighestEquiv_literal] at hv hw
  rw [← hv,← hw,rankTwoTypeIITripleEquiv_isometry q hq hq1]

end AMSPhysical
#print axioms AMSPhysical.rankTwoTypeIIHighestEquiv_inverse_isometry
