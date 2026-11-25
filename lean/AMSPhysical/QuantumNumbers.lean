import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AMSPhysical

variable {K : Type*} [Field K]

/-- Conventional quantum integer on integer weights, independently of any 6j formula. -/
def qInteger (q : K) (n : ℤ) : K := (q^n-q^(-n))/(q-q⁻¹)

@[simp] theorem qInteger_zero (q : K) : qInteger q 0=0 := by simp [qInteger]

theorem qInteger_one (q : K) (hden : q-q⁻¹≠0) : qInteger q 1=1 := by
  simp [qInteger,hden]

theorem qInteger_neg (q : K) (n : ℤ) : qInteger q (-n)= -qInteger q n := by
  unfold qInteger
  simp only [neg_neg]
  ring

theorem qInteger_add (q : K) (hq : q≠0) (m n : ℤ) :
    qInteger q (m+n)=q^m*qInteger q n+q^(-n)*qInteger q m := by
  simp only [qInteger,zpow_add₀ hq,neg_add,zpow_neg]
  have hm := zpow_ne_zero m hq
  have hn := zpow_ne_zero n hq
  field_simp
  ring

theorem qInteger_recurrence (q : K) (hq : q≠0) (n : ℤ) :
    qInteger q (n+1)+qInteger q (n-1)=(q+q⁻¹)*qInteger q n := by
  simp only [qInteger,sub_eq_add_neg,zpow_add₀ hq,zpow_neg,zpow_one,neg_add,
    neg_neg,zpow_neg_one]
  have hn := zpow_ne_zero n hq
  field_simp
  ring

/-- The coefficient identity needed for the genuine U_q(sl_2) commutator. -/
theorem qInteger_cross (q : K) (hq : q≠0) (hden : q-q⁻¹≠0) (m n : ℤ) :
    qInteger q (m+1)*qInteger q n-qInteger q m*qInteger q (n+1)=qInteger q (n-m) := by
  have he := qInteger_add q hq n (-m)
  simp only [qInteger_neg,neg_neg] at he
  rw [qInteger_add q hq m 1,qInteger_add q hq n 1,qInteger_one q hden]
  rw [sub_eq_add_neg n m,he]
  ring

end AMSPhysical

#print axioms AMSPhysical.qInteger_cross
