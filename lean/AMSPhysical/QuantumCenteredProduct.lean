import QuantumNumbers

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

theorem qInteger_centered_product_difference (q : ℝ) (hq : q≠0) (L a b : ℤ) :
    qInteger q a*qInteger q (L-a)-qInteger q b*qInteger q (L-b)=
      qInteger q (a-b)*qInteger q (L-a-b) := by
  simp only [qInteger,sub_eq_add_neg,neg_add,neg_neg,zpow_add₀ hq,zpow_neg]
  field_simp
  ring

end AMSPhysical
