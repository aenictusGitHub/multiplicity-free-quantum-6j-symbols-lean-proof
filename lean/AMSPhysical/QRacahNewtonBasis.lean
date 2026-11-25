import QRacahNewtonAlgebra

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem qPochhammer_cons (Q a : ℝ) (k : ℕ) :
    qPochhammer Q a (k+1)=(1-a)*qPochhammer Q (a*Q) k := by
  rw [qPochhammer_succ,← qPochhammer_shift]

theorem qPochhammer_two_shifts (Q a b : ℝ) (k : ℕ) :
    (1-b)*(qPochhammer Q a (k+1)*qPochhammer Q (b*Q) (k+1))=
      (1-a)*qPochhammer Q (a*Q) k*qPochhammer Q b k*(1-b*Q^k)*(1-b*Q^(k+1)) := by
  rw [qPochhammer_cons Q a k]
  calc
    _=(1-a)*qPochhammer Q (a*Q) k*((1-b)*qPochhammer Q (b*Q) (k+1)) := by ring
    _=(1-a)*qPochhammer Q (a*Q) k*qPochhammer Q b (k+2)  := by rw [← qPochhammer_cons Q b (k+1)]
    _=_ := by rw [qPochhammer_succ,qPochhammer_succ];ring

def qRacahNewton (Q c t : ℝ) (k : ℕ) : ℝ :=
  qPochhammer Q t⁻¹ k*qPochhammer Q (c*Q*t) k

theorem qRacahNewton_zero (Q c t : ℝ) : qRacahNewton Q c t 0=1 := by
  simp only [qRacahNewton,qPochhammer_zero,mul_one]

theorem qRacahNewton_succ (Q c t : ℝ) (k : ℕ) :
    qRacahNewton Q c t (k+1)=(1-Q^k/t)*(1-c*Q^(k+1)*t)*qRacahNewton Q c t k := by
  unfold qRacahNewton
  rw [qPochhammer_succ,qPochhammer_succ,pow_succ]
  simp only [div_eq_mul_inv]
  ring

theorem qRacahNewton_forward (Q c t : ℝ) (hQ : Q≠0) (ht : t≠0) (k : ℕ) :
    (1-c*Q*t)*qRacahNewton Q c (Q*t) (k+1)=
      (1-1/(Q*t))*(1-c*Q^(k+1)*t)*(1-c*Q^(k+2)*t)*qRacahNewton Q c t k := by
  have h := qPochhammer_two_shifts Q ((Q*t)⁻¹) (c*Q*t) k
  have ha : (Q*t)⁻¹*Q=t⁻¹ := by field_simp
  have hb : (c*Q*t)*Q=c*Q*(Q*t) := by ring
  rw [ha,hb] at h
  unfold qRacahNewton
  calc
    _=_ := h
    _=_ := by simp only [pow_succ,one_div];ring

theorem qRacahNewton_backward (Q c t : ℝ) (hQ : Q≠0) (ht : t≠0) (k : ℕ) :
    (1-t⁻¹)*qRacahNewton Q c (t/Q) (k+1)=
      (1-Q^k/t)*(1-Q^(k+1)/t)*(1-c*t)*qRacahNewton Q c t k := by
  have h := qPochhammer_two_shifts Q (c*t) t⁻¹ k
  have ha : (t/Q)⁻¹=t⁻¹*Q := by field_simp
  have hb : c*Q*(t/Q)=c*t := by field_simp
  have hc : (c*t)*Q=c*Q*t := by ring
  rw [hc] at h
  unfold qRacahNewton
  rw [ha,hb,mul_comm (qPochhammer Q (t⁻¹*Q) (k+1)) (qPochhammer Q (c*t) (k+1)),h]
  simp only [div_eq_mul_inv]
  ring

/-- Direct q-Pochhammer proof of the bidiagonal q-Racah operator on the Newton basis. -/
theorem qRacahNewton_difference (Q A B C D t : ℝ) (hQ : Q≠0) (ht : t≠0)
    (hd0 : 1-C*D*t^2≠0) (hd1 : 1-C*D*Q*t^2≠0) (hd2 : 1-C*D*Q^2*t^2≠0) (k : ℕ) :
    qRacahB Q A B C D t*(qRacahNewton Q (C*D) (Q*t) (k+1)-qRacahNewton Q (C*D) t (k+1))+
      qRacahD Q A B C D t*(qRacahNewton Q (C*D) (t/Q) (k+1)-qRacahNewton Q (C*D) t (k+1))=
      qRacahLambda Q A B (Q^(k+1))*qRacahNewton Q (C*D) t (k+1)+
        qRacahNu A B C D (Q^(k+1))*qRacahNewton Q (C*D) t k := by
  have hz : Q^(k+1)/(Q*t)=Q^k/t := by rw [pow_succ];field_simp
  apply qRacah_newton_algebra Q A B C D t (Q^(k+1)) _ _ _ _ hQ ht (pow_ne_zero _ hQ) hd0 hd1 hd2
  · rw [hz]
    exact qRacahNewton_succ Q (C*D) t k
  · have h := qRacahNewton_forward Q (C*D) t hQ ht k
    have hp : (C*D)*Q^(k+2)*t=C*D*Q*(Q^(k+1))*t := by rw [pow_succ];ring
    rw [hp] at h
    exact h
  · rw [hz]
    exact qRacahNewton_backward Q (C*D) t hQ ht k

end AMSPhysical

#print axioms AMSPhysical.qRacahNewton_difference
