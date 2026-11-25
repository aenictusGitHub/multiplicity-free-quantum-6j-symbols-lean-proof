import OccupationTripleCoefficients
import QuantumMixedMetric
import FiniteWeightedDuality

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

def physicalTripleWeight (q : ℝ) (n l m c : ℕ) (p : OccupationTripleIndex n l m c) : ℝ :=
  occupationCompactWeight q n l p.1*occupationOppositeWeight q n m p.2.1*occupationCompactWeight q n c p.2.2

theorem physicalTripleWeight_pos (q : ℝ) (hq : 0<q) (n l m c : ℕ) (p : OccupationTripleIndex n l m c) :
    0<physicalTripleWeight q n l m c p :=
  mul_pos (mul_pos (occupationCompactWeight_pos q hq n l p.1) (occupationOppositeWeight_pos q hq n m p.2.1))
    (occupationCompactWeight_pos q hq n c p.2.2)

def physicalTripleBilin (q : ℝ) (n l m c : ℕ) :
    quantumOccupationTripleSpace n l m c →ₗ[ℝ] quantumOccupationTripleSpace n l m c →ₗ[ℝ] ℝ := by
  let V := quantumOccupationTripleSpace n l m c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact finiteWeightedBilin (V:=V) (physicalTripleWeight q n l m c) (occupationTripleBasis n l m c).equivFun.toLinearMap

theorem physicalTripleBilin_symm (q : ℝ) (n l m c : ℕ) (v w : quantumOccupationTripleSpace n l m c) :
    physicalTripleBilin q n l m c v w=physicalTripleBilin q n l m c w v := by
  let V := quantumOccupationTripleSpace n l m c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact finiteWeightedPair_symm (V:=V) (physicalTripleWeight q n l m c)
    (occupationTripleBasis n l m c).equivFun.toLinearMap v w

theorem physicalTripleBilin_definite (q : ℝ) (hq : 0<q) (n l m c : ℕ)
    (v : quantumOccupationTripleSpace n l m c) (hv : physicalTripleBilin q n l m c v v=0) : v=0 := by
  let V := quantumOccupationTripleSpace n l m c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact finiteWeightedPair_definite (V:=V) (physicalTripleWeight q n l m c)
    (physicalTripleWeight_pos q hq n l m c) (occupationTripleBasis n l m c).equivFun.toLinearMap
    (occupationTripleBasis n l m c).equivFun.injective v hv

theorem physicalTripleBilin_nonneg (q : ℝ) (hq : 0<q) (n l m c : ℕ) (v : quantumOccupationTripleSpace n l m c) :
    0 ≤ physicalTripleBilin q n l m c v v := by
  let V := quantumOccupationTripleSpace n l m c
  letI : AddCommGroup V := inferInstance
  letI : Module ℝ V := inferInstance
  exact finiteWeightedPair_nonneg (V:=V) _ (fun p =>(physicalTripleWeight_pos q hq n l m c p).le) _ v

end AMSPhysical
