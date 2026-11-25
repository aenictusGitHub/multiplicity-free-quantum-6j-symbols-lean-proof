import PhysicalTypeICouplingVectors
import RankTwoHighestCouplingEigenvectors
import QuantumCompleteHighestSimpleSpectrum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

theorem physicalTypeILeftCoupling_eigen (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) (t : QuantumCupIndex l m c) :
    completeHighestLeftAction q hq hq1 n hn l m h c hadm hRank
      (physicalTypeILeftCoupling q hq hq1 n hn l m h c hadm hRank t)=
      quantumCupLeftEigenvalue q n l m h t.val.val • physicalTypeILeftCoupling q hq hq1 n hn l m h c hadm hRank t := by
  apply (fullPhysicalHighestRankReduction q hq hq1 n hn l m h c hadm hRank).injective
  rw [fullPhysicalHighestRankReduction_left q hq hq1,map_smul,physicalTypeILeftCoupling_rank_image]
  have hLam : quantumCupLeftEigenvalue q n l m h t.val.val=
      quantumCupLeftEigenvalue q 1 l m (h+n-1) t.val.val :=
    (quantumCupLeftEigenvalue_standard_shift q n hn l m h t.val.val).trans
      (quantumCupLeftEigenvalue_middle_add q 1 l m (h+n-1) t.val.val).symm
  rw [hLam]
  exact rankTwoHighestLeftCoupling_eigen q hq hq1 l m (h+n-1) c hadm t

theorem physicalTypeIRightCoupling_eigen (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m h c : ℕ) (hadm : m≤l+c) (hRank : h=0 ∨ n=1) (t : QuantumCupIndex l m c) :
    completeHighestRightAction q hq hq1 n hn l m h c hadm hRank
      (physicalTypeIRightCoupling q hq hq1 n hn l m h c hadm hRank t)=
      quantumCupLeftEigenvalue q n c m h (m-t.val.val) • physicalTypeIRightCoupling q hq hq1 n hn l m h c hadm hRank t := by
  apply (fullPhysicalHighestRankReduction q hq hq1 n hn l m h c hadm hRank).injective
  rw [fullPhysicalHighestRankReduction_right q hq hq1,map_smul,physicalTypeIRightCoupling_rank_image]
  have hLam : quantumCupLeftEigenvalue q n c m h (m-t.val.val)=
      quantumCupLeftEigenvalue q 1 c m (h+n-1) (m-t.val.val) :=
    (quantumCupLeftEigenvalue_standard_shift q n hn c m h (m-t.val.val)).trans
      (quantumCupLeftEigenvalue_middle_add q 1 c m (h+n-1) (m-t.val.val)).symm
  rw [hLam]
  exact rankTwoHighestRightCoupling_eigen q hq hq1 l m (h+n-1) c hadm t

end AMSPhysical
#print axioms AMSPhysical.physicalTypeILeftCoupling_eigen
#print axioms AMSPhysical.physicalTypeIRightCoupling_eigen
