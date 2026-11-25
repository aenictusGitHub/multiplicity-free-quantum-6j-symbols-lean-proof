import QRacahNewtonAlgebra

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 12000000
set_option maxRecDepth 4096
noncomputable section
namespace AMSPhysical

def qRacahBRegularized (Q A B t : ℝ) : ℝ :=
  (1-A*Q*t)*(1-B*A*Q*t)*(1-A^2*Q*t)/((1-A^2*Q*t^2)*(1+A*Q*t))

/-- The removable forward-coefficient singularity agrees with total division,
including its zero-spin endpoint value. -/
theorem qRacahB_regularized (Q A B t : ℝ) :
    qRacahB Q A B A A t=qRacahBRegularized Q A B t := by
  unfold qRacahB qRacahBRegularized
  have hd : 1-A*A*Q^2*t^2=(1-A*Q*t)*(1+A*Q*t) := by ring
  rw [hd]
  by_cases hx : 1-A*Q*t=0
  · simp only [hx,zero_mul,zero_div]
  · have hn : (1-A*Q*t)*(1-B*A*Q*t)*(1-A*Q*t)*(1-A*A*Q*t)=
        ((1-A*Q*t)*(1-B*A*Q*t)*(1-A^2*Q*t))*(1-A*Q*t) := by ring
    have hden : (1-A*A*Q*t^2)*((1-A*Q*t)*(1+A*Q*t))=
        ((1-A^2*Q*t^2)*(1+A*Q*t))*(1-A*Q*t) := by ring
    rw [hn,hden,mul_div_mul_right _ _ hx]

/-- Cleared Newton-basis certificate with the removable singularity canceled.
It does not assume 1-A^2 Q^2 t^2 is nonzero. -/
theorem qRacah_newton_regularized_algebra (Q A B t z f fp fm f1 : ℝ)
    (hQ : Q≠0) (ht : t≠0) (hz : z≠0)
    (hd0 : 1-A^2*t^2≠0) (hd1 : 1-A^2*Q*t^2≠0) (hdp : 1+A*Q*t≠0)
    (h0 : f1=(1-z/(Q*t))*(1-A^2*z*t)*f)
    (hp : (1-A^2*Q*t)*fp=(1-1/(Q*t))*(1-A^2*z*t)*(1-A^2*Q*z*t)*f)
    (hm : (1-t⁻¹)*fm=(1-z/(Q*t))*(1-z/t)*(1-A^2*t)*f) :
    qRacahBRegularized Q A B t*(fp-f1)+qRacahD Q A B A A t*(fm-f1)=
      qRacahLambda Q A B z*f1+qRacahNu A B A A z*f := by
  linear_combination (norm := skip)
    ((1-A*Q*t)*(1-B*A*Q*t)/((1-A^2*Q*t^2)*(1+A*Q*t)))*hp+
    (-Q*t*(1-A*t)*(B-A*t)*(A-A^2*t)/((1-A^2*t^2)*(1-A^2*Q*t^2)))*hm-
    (qRacahBRegularized Q A B t+qRacahD Q A B A A t+qRacahLambda Q A B z)*h0
  unfold qRacahBRegularized qRacahD qRacahLambda qRacahNu
  have hn0 : 1-t^2*A^2≠0 := by convert hd0 using 1 <;> ring
  have hn1 : 1-Q*t^2*A^2≠0 := by convert hd1 using 1 <;> ring
  have hnp : 1+Q*t*A≠0 := by convert hdp using 1 <;> ring
  field_simp [hQ,ht,hz,hd0,hd1,hdp,hn0,hn1,hnp] <;> ring

end AMSPhysical

#print axioms AMSPhysical.qRacahB_regularized
#print axioms AMSPhysical.qRacah_newton_regularized_algebra
