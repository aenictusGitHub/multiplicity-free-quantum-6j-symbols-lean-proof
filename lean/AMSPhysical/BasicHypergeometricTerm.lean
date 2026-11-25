import QShiftedFactorial

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

def basic3Term (Q A B U C D : ℝ) (k : ℕ) : ℝ :=
  qPochhammer Q A k*qPochhammer Q B k*qPochhammer Q U k*Q^k/
    (qPochhammer Q Q k*qPochhammer Q C k*qPochhammer Q D k)

theorem basic3Term_succ (Q A B U C D : ℝ) (k : ℕ) :
    basic3Term Q A B U C D (k+1)=basic3Term Q A B U C D k*
      (Q*(1-A*Q^k)*(1-B*Q^k)*(1-U*Q^k)/((1-Q*Q^k)*(1-C*Q^k)*(1-D*Q^k))) := by
  unfold basic3Term
  simp only [qPochhammer_succ,pow_succ']
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem basic3Term_shift (Q A B U C D : ℝ) (k : ℕ)
    (hU : 1-U≠0) (hD : 1-D≠0)
    (hQp : qPochhammer Q Q k≠0) (hCp : qPochhammer Q C k≠0) (hDp : qPochhammer Q D k≠0) :
    basic3Term Q A B (U*Q) C (D*Q) k=basic3Term Q A B U C D k*
      ((1-U*Q^k)*(1-D)/((1-U)*(1-D*Q^k))) := by
  have hUn : qPochhammer Q (U*Q) k=qPochhammer Q U k*(1-U*Q^k)/(1-U) := by
    apply (eq_div_iff hU).mpr
    simpa only [mul_comm] using qPochhammer_shift Q U k
  have hDn : qPochhammer Q (D*Q) k=qPochhammer Q D k*(1-D*Q^k)/(1-D) := by
    apply (eq_div_iff hD).mpr
    simpa only [mul_comm] using qPochhammer_shift Q D k
  unfold basic3Term
  rw [hUn,hDn]
  field_simp

end AMSPhysical

#print axioms AMSPhysical.basic3Term_shift
