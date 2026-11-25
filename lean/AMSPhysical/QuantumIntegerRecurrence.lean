import QuantumNumbers

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical

variable {K : Type*} [Field K]

theorem qInteger_second_order (q : K) (hq : q≠0) (hD : q-q⁻¹≠0) (a : ℤ) :
    qInteger q (a+1)+qInteger q (a-1)=(q+q⁻¹)*qInteger q a := by
  have hp := qInteger_add q hq a 1
  have hm := qInteger_add q hq a (-1)
  have hminus : qInteger q (-1)= -(1:K) := by rw [qInteger_neg,qInteger_one q hD]
  simp only [qInteger_one q hD,zpow_neg_one,mul_one] at hp
  have hpow : q^(-(-1:ℤ))=q := by norm_num
  rw [hminus,hpow] at hm
  have ha : a-1=a+(-1) := by ring
  rw [ha,hm,hp]
  ring

end AMSPhysical

#print axioms AMSPhysical.qInteger_second_order
