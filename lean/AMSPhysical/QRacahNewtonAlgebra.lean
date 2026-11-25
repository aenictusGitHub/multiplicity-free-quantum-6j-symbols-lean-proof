import QShiftedFactorial

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 8000000
noncomputable section
namespace AMSPhysical

def qRacahB (Q A B C D t : ℝ) : ℝ :=
  (1-A*Q*t)*(1-B*D*Q*t)*(1-C*Q*t)*(1-C*D*Q*t)/
    ((1-C*D*Q*t^2)*(1-C*D*Q^2*t^2))

def qRacahD (Q A B C D t : ℝ) : ℝ :=
  Q*(1-t)*(1-D*t)*(B-C*t)*(A-C*D*t)/((1-C*D*t^2)*(1-C*D*Q*t^2))

def qRacahLambda (Q A B z : ℝ) : ℝ := (z⁻¹-1)*(1-A*B*Q*z)
def qRacahNu (A B C D z : ℝ) : ℝ := (1-z⁻¹)*(1-A*z)*(1-B*D*z)*(1-C*z)

/-- Polynomial certificate for the q-Racah operator on its Newton basis.
No nonvanishing of a Newton basis value, or of its boundary factors, is assumed. -/
theorem qRacah_newton_algebra (Q A B C D t z f fp fm f1 : ℝ)
    (hQ : Q≠0) (ht : t≠0) (hz : z≠0)
    (hd0 : 1-C*D*t^2≠0) (hd1 : 1-C*D*Q*t^2≠0) (hd2 : 1-C*D*Q^2*t^2≠0)
    (h0 : f1=(1-z/(Q*t))*(1-C*D*z*t)*f)
    (hp : (1-C*D*Q*t)*fp=(1-1/(Q*t))*(1-C*D*z*t)*(1-C*D*Q*z*t)*f)
    (hm : (1-t⁻¹)*fm=(1-z/(Q*t))*(1-z/t)*(1-C*D*t)*f) :
    qRacahB Q A B C D t*(fp-f1)+qRacahD Q A B C D t*(fm-f1)=
      qRacahLambda Q A B z*f1+qRacahNu A B C D z*f := by
  linear_combination (norm := skip)
    ((1-A*Q*t)*(1-B*D*Q*t)*(1-C*Q*t)/((1-C*D*Q*t^2)*(1-C*D*Q^2*t^2)))*hp+
    (-Q*t*(1-D*t)*(B-C*t)*(A-C*D*t)/((1-C*D*t^2)*(1-C*D*Q*t^2)))*hm-
    (qRacahB Q A B C D t+qRacahD Q A B C D t+qRacahLambda Q A B z)*h0
  unfold qRacahB qRacahD qRacahLambda qRacahNu
  have hn0 : 1-t^2*D*C≠0 := by convert hd0 using 1 <;> ring
  have hn1 : 1-Q*t^2*D*C≠0 := by convert hd1 using 1 <;> ring
  have hn2 : 1-Q^2*t^2*D*C≠0 := by convert hd2 using 1 <;> ring
  field_simp [hQ,ht,hz,hd0,hd1,hd2,hn0,hn1,hn2] <;> ring

end AMSPhysical

#print axioms AMSPhysical.qRacah_newton_algebra
