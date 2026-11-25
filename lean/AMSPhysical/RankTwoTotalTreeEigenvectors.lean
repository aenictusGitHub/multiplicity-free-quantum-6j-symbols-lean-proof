import RankTwoTreeRadialEigenvectors
import QuantumTripleZeroBoundaries

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical

theorem rankTwoLeftTree_total_radial (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m c : ℕ)
    (r : MixedFusionIndex l m) (s : Fin (min (coupledLabel l m r) c+1))
    (v : RealQuantumSpace (coupledLabel (coupledLabel l m r) c s)) :
    physicalTripleLeftRadialTotal q 1 l m c
      (rankTwoMixedTripleEquiv l m c (quantumLeftTreeMap q hq hq1 l m c r s v))=
      quantumCupLeftEigenvalue q 1 l m 0 r.val •
        rankTwoMixedTripleEquiv l m c (quantumLeftTreeMap q hq hq1 l m c r s v) := by
  cases l with
  | zero =>
    have hr : r.val=0 := by have hh:=r.isLt;simpa using Nat.eq_zero_of_le_zero (by omega : r.val≤0)
    rw [physicalTripleLeftRadialTotal_zero_first]
    simp [quantumCupLeftEigenvalue,hr]
  | succ l =>
    cases m with
    | zero =>
      have hr : r.val=0 := by have hh:=r.isLt;omega
      rw [physicalTripleLeftRadialTotal_zero_middle]
      simp [quantumCupLeftEigenvalue,hr]
    | succ m =>
      rw [physicalTripleLeftRadialTotal_positive]
      exact rankTwoLeftTree_radial q hq hq1 l m c r s v

theorem rankTwoRightTree_total_radial (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m c : ℕ)
    (r : MixedFusionIndex m c) (s : Fin (min l (coupledLabel m c r)+1))
    (v : RealQuantumSpace (coupledLabel l (coupledLabel m c r) s)) :
    physicalTripleRightRadialTotal q 1 l m c
      (rankTwoMixedTripleEquiv l m c (quantumRightTreeMap q hq hq1 l m c r s v))=
      quantumCupLeftEigenvalue q 1 m c 0 r.val •
        rankTwoMixedTripleEquiv l m c (quantumRightTreeMap q hq hq1 l m c r s v) := by
  cases m with
  | zero =>
    have hr : r.val=0 := by have hh:=r.isLt;omega
    rw [physicalTripleRightRadialTotal_zero_middle]
    simp [quantumCupLeftEigenvalue,hr]
  | succ m =>
    cases c with
    | zero =>
      have hr : r.val=0 := by have hh:=r.isLt;omega
      rw [physicalTripleRightRadialTotal_zero_third]
      simp [quantumCupLeftEigenvalue,hr]
    | succ c =>
      rw [physicalTripleRightRadialTotal_positive]
      exact rankTwoRightTree_radial q hq hq1 l m c r s v

end AMSPhysical
#print axioms AMSPhysical.rankTwoLeftTree_total_radial
#print axioms AMSPhysical.rankTwoRightTree_total_radial
