import QuantumNumbers
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 900000
namespace AMSPhysical

/-- Cleared adjacent-coefficient identity for the proposed two-term Type-II
creation calculation. This scalar identity alone does not identify the
physical operator or establish its support bounds. -/
theorem qInteger_typeII_adjacent_scalar (q:ℝ) (hq:q≠0) (hD:q-q⁻¹≠0) (p x y:ℤ) :
    qInteger q (p+x)*qInteger q (x+1)*qInteger q (y+1)-
      q*qInteger q (p+x+1)*qInteger q x*qInteger q y-
      q^(p-y)*qInteger q (p+x)*qInteger q (p+x+1)=
    -q^(p+x+1)*qInteger q p*qInteger q (p+x-y) := by
  have hQ:q^2-1≠0:=by
    intro hz
    apply hD
    apply (mul_left_cancel₀ hq)
    rw [mul_sub,mul_inv_cancel₀ hq,mul_zero,← pow_two]
    exact hz
  have hQ':-1+q^2≠0:=by simpa only [sub_eq_add_neg,add_comm] using hQ
  apply (mul_left_cancel₀ (pow_ne_zero 3 hD))
  unfold qInteger
  field_simp [hD]
  simp only [zpow_add₀ hq,zpow_sub₀ hq,zpow_neg,zpow_one]
  field_simp [hq,hD,zpow_ne_zero p hq,zpow_ne_zero x hq,zpow_ne_zero y hq]
  ring_nf

end AMSPhysical
#print axioms AMSPhysical.qInteger_typeII_adjacent_scalar
