import QuantumTwoRowDimensionDifference
import QuantumTwoRowWeylScalar

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

/-- Closed quantum Weyl dimension of the ACTUAL canonical two-row irrep,
proved from its literal pivotal trace and full symmetric tensor fusion. -/
theorem twoRowIrrepQuantumDimension_closed (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b : ℕ) :
    twoRowIrrepQuantumDimension q hq hq1 n hn a b=
      qnum q (a+1)*qfactorial q (a+b+n)*qfactorial q (b+n-1)/
        (qfactorial q (a+b+1)*qfactorial q b*qfactorial q n*qfactorial q (n-1)) := by
  change twoRowIrrepQuantumDimension q hq hq1 n hn a b=twoRowWeylDimension q n a b
  cases b with
  | zero => rw [twoRowIrrepQuantumDimension_right_zero q hq hq1,twoRowWeylDimension_right_zero q hq n hn]
  | succ b => rw [twoRowIrrepQuantumDimension_succ q hq hq1,twoRowWeylDimension_succ_difference q hq hq1 n hn]

theorem twoRowIrrepQuantumDimension_pos (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b : ℕ) : 0<twoRowIrrepQuantumDimension q hq hq1 n hn a b := by
  rw [twoRowIrrepQuantumDimension_closed q hq hq1 n hn]
  exact div_pos (mul_pos (mul_pos (qnum_pos q hq (a+1) (by omega))
    (qfactorial_pos q hq _)) (qfactorial_pos q hq _))
    (mul_pos (mul_pos (mul_pos (qfactorial_pos q hq _) (qfactorial_pos q hq b))
      (qfactorial_pos q hq n)) (qfactorial_pos q hq (n-1)))

theorem sameWeyl_actual_dimension (q : ℝ) (hq : 0<q) (hq1 : q≠1) (h p r t : ℕ) :
    sameWeyl (qfactorial q) (qnum q) h p r t=
      twoRowIrrepQuantumDimension q hq hq1 (h+1) (by omega) (p+r) t := by
  rw [twoRowIrrepQuantumDimension_closed q hq hq1]
  unfold sameWeyl factorialConstant
  simp only [Nat.add_sub_cancel]
  rw [show p+r+t+h+1=(p+r)+t+(h+1) from by omega,
    show t+(h+1)-1=t+h from by omega]
  ring

end AMSPhysical
#print axioms AMSPhysical.twoRowIrrepQuantumDimension_closed
#print axioms AMSPhysical.sameWeyl_actual_dimension
