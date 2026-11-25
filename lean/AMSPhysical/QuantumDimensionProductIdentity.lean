import QuantumNumbers
import QuantumAnalyticCoefficients

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical

theorem qInteger_shift_product (q : ℝ) (hq : q≠0) (a b n : ℤ) :
    qInteger q (a+n)*qInteger q (b+n)-qInteger q a*qInteger q b=
      qInteger q n*qInteger q (a+b+n) := by
  simp only [qInteger,zpow_add₀ hq,neg_add,zpow_neg]
  field_simp
  ring

theorem qnum_shift_product (q : ℝ) (hq : 0<q) (hq1 : q≠1) (a b n : ℕ) :
    qnum q (a+n)*qnum q (b+n)-qnum q a*qnum q b=qnum q n*qnum q (a+b+n) := by
  simpa only [qnum_eq_qInteger q hq hq1,Nat.cast_add] using
    qInteger_shift_product q (ne_of_gt hq) (a:ℤ) (b:ℤ) (n:ℤ)

end AMSPhysical
