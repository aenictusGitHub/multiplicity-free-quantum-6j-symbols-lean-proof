import QShiftedProducts

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

/-- Exact product cancellation underlying the terminating Sears convolution.
No q-Pochhammer factor is assumed nonzero. -/
theorem sears_product_cancellation (Q x : ℝ) (hQ : Q≠0) (hx : x≠0)
    (k j : ℕ) (hj : j≤k) :
    qPochhammer Q (Q^(-(k:ℤ))) j*qPochhammer Q x k*qPochhammer Q Q (k-j)*Q^j=
      x^j*qPochhammer Q Q k*qPochhammer Q x (k-j)*qPochhammer Q (Q^(1-(k:ℤ))/x) j := by
  have hQsplit := qPochhammer_reflected_suffix Q Q hQ hQ k j hj
  have hXsplit := qPochhammer_reflected_suffix Q x hQ hx k j hj
  have harg : Q^(1-(k:ℤ))/Q=Q^(-(k:ℤ)) := by
    rw [zpow_sub₀ hQ,zpow_one,zpow_neg]
    field_simp [hQ,zpow_ne_zero (k:ℤ) hQ]
  rw [harg] at hQsplit
  have hp : (-(x*Q^(k-j)))^j*Q^j=x^j*(-(Q*Q^(k-j)))^j := by
    rw [← mul_pow,← mul_pow]
    congr 1
    ring
  rw [hXsplit,hQsplit]
  linear_combination qPochhammer Q (Q^(-(k:ℤ))) j*qPochhammer Q x (k-j)*
    Q^(j.choose 2)*qPochhammer Q (Q^(1-(k:ℤ))/x) j*qPochhammer Q Q (k-j)*hp

end AMSPhysical

#print axioms AMSPhysical.sears_product_cancellation
