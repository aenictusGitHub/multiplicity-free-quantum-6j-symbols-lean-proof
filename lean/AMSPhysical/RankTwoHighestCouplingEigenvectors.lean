import StandardCupHighestVectors
import RankTwoTotalTreeEigenvectors
import QuantumCupStandardEigenvalues

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

theorem rankTwoHighestLeftCoupling_eigen (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (l m b c : ℕ) (hadm : m≤l+c) (t : QuantumCupIndex l m c) :
    completeHighestLeftAction q hq hq1 1 (by omega) l m b c hadm (Or.inr rfl)
      (rankTwoHighestEquiv q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
        l (m+b) c (l+c-m+b) (standardCupLeftHighest q hq hq1 l m b c hadm t))=
      quantumCupLeftEigenvalue q 1 l m b t.val.val •
        rankTwoHighestEquiv q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
          l (m+b) c (l+c-m+b) (standardCupLeftHighest q hq hq1 l m b c hadm t) := by
  apply Subtype.ext
  rw [completeHighestLeftAction_ambient]
  simp only [Submodule.coe_smul_of_tower,rankTwoHighestEquiv_literal]
  rw [quantumCupLeftEigenvalue_middle_add]
  exact rankTwoLeftTree_total_radial q hq hq1 l (m+b) c
    (quantumCupLeftPath l m b c t).1 (quantumCupLeftPath l m b c t).2 _

theorem rankTwoHighestRightCoupling_eigen (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (l m b c : ℕ) (hadm : m≤l+c) (t : QuantumCupIndex l m c) :
    completeHighestRightAction q hq hq1 1 (by omega) l m b c hadm (Or.inr rfl)
      (rankTwoHighestEquiv q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
        l (m+b) c (l+c-m+b) (standardCupRightHighest q hq hq1 l m b c hadm t))=
      quantumCupLeftEigenvalue q 1 c m b (m-t.val.val) •
        rankTwoHighestEquiv q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
          l (m+b) c (l+c-m+b) (standardCupRightHighest q hq hq1 l m b c hadm t) := by
  apply Subtype.ext
  rw [completeHighestRightAction_ambient]
  simp only [Submodule.coe_smul_of_tower,rankTwoHighestEquiv_literal]
  rw [quantumCupLeftEigenvalue_middle_add,quantumCupLeftEigenvalue_swap]
  exact rankTwoRightTree_total_radial q hq hq1 l (m+b) c
    (quantumCupRightPath l m b c t).1 (quantumCupRightPath l m b c t).2 _

end AMSPhysical
#print axioms AMSPhysical.rankTwoHighestLeftCoupling_eigen
#print axioms AMSPhysical.rankTwoHighestRightCoupling_eigen
