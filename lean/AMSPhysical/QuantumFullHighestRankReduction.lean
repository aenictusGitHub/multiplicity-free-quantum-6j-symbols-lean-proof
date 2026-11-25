import QuantumCupHighestComplete
import QuantumPhysicalCupUnitary

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

/-- The rank-reduction isometry now acts on the ENTIRE independently defined
physical highest-weight multiplicity spaces, not merely on a cup subspace. -/
def fullPhysicalHighestRankReduction (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) :
    typeAHighestSpace (V:=quantumOccupationTripleSpace n l (m+h) c) q n
      (typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l (m+h) c)
      (mixedHighestDynkin n (l+c-m+h) 0) ≃ₗ[ℝ]
      typeAHighestSpace (V:=quantumOccupationTripleSpace 1 l (m+(h+n-1)) c) q 1
        (typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 l (m+(h+n-1)) c)
        (mixedHighestDynkin 1 (l+c-m+(h+n-1)) 0) := by
  let V := quantumOccupationTripleSpace n l (m+h) c
  let W := quantumOccupationTripleSpace 1 l (m+(h+n-1)) c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  exact (LinearEquiv.ofEq _ _ (physicalQuantumCupSpan_eq_highest q hq hq1 n hn l m h c hadm hRank).symm).trans
    ((physicalQuantumCupUnitaryRankReduction q hq n hn l m h c hadm).trans
      (LinearEquiv.ofEq _ _ (physicalQuantumCupSpan_eq_highest q hq hq1 1 (by omega) l m (h+n-1) c hadm (Or.inr rfl))))

theorem fullPhysicalHighestRankReduction_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1)
    (v w : typeAHighestSpace (V:=quantumOccupationTripleSpace n l (m+h) c) q n
      (typeAMixedTriple q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) n l (m+h) c)
      (mixedHighestDynkin n (l+c-m+h) 0)) :
    physicalTripleBilin q 1 l (m+(h+n-1)) c
      (fullPhysicalHighestRankReduction q hq hq1 n hn l m h c hadm hRank v).val
      (fullPhysicalHighestRankReduction q hq hq1 n hn l m h c hadm hRank w).val=
      physicalTripleBilin q n l (m+h) c v.val w.val := by
  unfold fullPhysicalHighestRankReduction
  simp only [LinearEquiv.trans_apply,LinearEquiv.coe_ofEq_apply]
  exact physicalQuantumCupUnitaryRankReduction_isometry q hq hq1 n hn l m h c hadm _ _

end AMSPhysical
#print axioms AMSPhysical.fullPhysicalHighestRankReduction_isometry
