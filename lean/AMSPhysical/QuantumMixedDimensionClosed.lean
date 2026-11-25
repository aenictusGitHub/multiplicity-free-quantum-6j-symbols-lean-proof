import QuantumMixedWeylScalar

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 180000
noncomputable section
namespace AMSPhysical

/-- The full quantum Weyl dimension formula for the ACTUAL constructed
mixed highest-weight irrep, proved from its pivotal trace and complete fusion. -/
theorem mixedIrrepQuantumDimension_closed (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b : ℕ) :
    mixedIrrepQuantumDimension q hq hq1 n hn a b=
      qnum q (a+b+n)*qfactorial q (a+n-1)*qfactorial q (b+n-1)/
        (qfactorial q a*qfactorial q b*qfactorial q n*qfactorial q (n-1)) := by
  change mixedIrrepQuantumDimension q hq hq1 n hn a b=mixedWeylDimension q n a b
  cases a with
  | zero => rw [mixedIrrepQuantumDimension_left_zero q hq hq1,mixedWeylDimension_left_zero q hq n hn]
  | succ a =>
    cases b with
    | zero => rw [mixedIrrepQuantumDimension_right_zero q hq hq1,mixedWeylDimension_swap,
        mixedWeylDimension_left_zero q hq n hn]
    | succ b => rw [mixedIrrepQuantumDimension_succ q hq hq1,mixedWeylDimension_succ_difference q hq hq1 n hn]

theorem mixedWeylDimension_pos (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (a b : ℕ) :
    0<mixedWeylDimension q n a b := by
  unfold mixedWeylDimension
  exact div_pos (mul_pos (mul_pos (qnum_pos q hq (a+b+n) (by omega))
    (qfactorial_pos q hq _)) (qfactorial_pos q hq _))
    (mul_pos (mul_pos (mul_pos (qfactorial_pos q hq a) (qfactorial_pos q hq b))
      (qfactorial_pos q hq n)) (qfactorial_pos q hq (n-1)))

theorem mixedIrrepQuantumDimension_pos (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (a b : ℕ) : 0<mixedIrrepQuantumDimension q hq hq1 n hn a b := by
  rw [mixedIrrepQuantumDimension_closed q hq hq1 n hn]
  exact mixedWeylDimension_pos q hq n hn a b

end AMSPhysical
#print axioms AMSPhysical.mixedIrrepQuantumDimension_closed
