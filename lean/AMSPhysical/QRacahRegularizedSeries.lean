import QRacahRegularizedAlgebra
import QRacahFiniteSeries

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem qRacahNewton_difference_regularized (Q A B t : ℝ) (hQ : Q≠0) (ht : t≠0)
    (hd0 : 1-A^2*t^2≠0) (hd1 : 1-A^2*Q*t^2≠0) (hdp : 1+A*Q*t≠0) (k : ℕ) :
    qRacahBRegularized Q A B t*(qRacahNewton Q (A*A) (Q*t) (k+1)-qRacahNewton Q (A*A) t (k+1))+
      qRacahD Q A B A A t*(qRacahNewton Q (A*A) (t/Q) (k+1)-qRacahNewton Q (A*A) t (k+1))=
      qRacahLambda Q A B (Q^(k+1))*qRacahNewton Q (A*A) t (k+1)+
        qRacahNu A B A A (Q^(k+1))*qRacahNewton Q (A*A) t k := by
  have hz : Q^(k+1)/(Q*t)=Q^k/t := by rw [pow_succ];field_simp
  apply qRacah_newton_regularized_algebra Q A B t (Q^(k+1)) _ _ _ _ hQ ht
    (pow_ne_zero _ hQ) hd0 hd1 hdp
  · rw [hz]
    simpa only [pow_two] using qRacahNewton_succ Q (A*A) t k
  · have h := qRacahNewton_forward Q (A*A) t hQ ht k
    have hp : (A*A)*Q^(k+2)*t=A*A*Q*(Q^(k+1))*t := by rw [pow_succ];ring
    rw [hp] at h
    simpa only [pow_two] using h
  · rw [hz]
    simpa only [pow_two] using qRacahNewton_backward Q (A*A) t hQ ht k

/-- The terminating q-Racah difference equation at the removable zero-spin
singularity, proved directly rather than assuming the generic denominator. -/
theorem qRacahSeries_difference_regularized (Q A B t : ℝ) (hQ : Q≠0) (ht : t≠0) (n : ℕ)
    (hreg : QRacahSeriesRegular Q A B A A n)
    (hd0 : 1-A^2*t^2≠0) (hd1 : 1-A^2*Q*t^2≠0) (hdp : 1+A*Q*t≠0) :
    qRacahB Q A B A A t*(qRacahSeries Q A B A A n (Q*t)-qRacahSeries Q A B A A n t)+
      qRacahD Q A B A A t*(qRacahSeries Q A B A A n (t/Q)-qRacahSeries Q A B A A n t)=
      qRacahLambda Q A B (Q^n)*qRacahSeries Q A B A A n t := by
  rw [qRacahB_regularized]
  have he := finite_bidiagonal_eigen n
    (qRacahCoefficient Q A B A A (Q^n)) (qRacahNewton Q (A*A) t)
    (fun k => qRacahBRegularized Q A B t*(qRacahNewton Q (A*A) (Q*t) k-qRacahNewton Q (A*A) t k)+
      qRacahD Q A B A A t*(qRacahNewton Q (A*A) (t/Q) k-qRacahNewton Q (A*A) t k))
    (fun k => qRacahLambda Q A B (Q^k)) (fun k => qRacahNu A B A A (Q^k)) (qRacahLambda Q A B (Q^n))
    (by simp only [qRacahNewton_zero,sub_self,mul_zero,add_zero,pow_zero,qRacahLambda,inv_one,zero_mul])
    (fun k hk => qRacahNewton_difference_regularized Q A B t hQ ht hd0 hd1 hdp k)
    (fun k hk => qRacahCoefficient_eigen_step Q A B A A (Q^n) hQ (pow_ne_zero _ hQ) k
      (hreg k hk).1 (hreg k hk).2.1 (hreg k hk).2.2.1 (hreg k hk).2.2.2) rfl
  calc
    _=(∑ k∈Finset.range (n+1),qRacahCoefficient Q A B A A (Q^n) k*
        (qRacahBRegularized Q A B t*(qRacahNewton Q (A*A) (Q*t) k-qRacahNewton Q (A*A) t k)+
          qRacahD Q A B A A t*(qRacahNewton Q (A*A) (t/Q) k-qRacahNewton Q (A*A) t k))) := by
      unfold qRacahSeries
      simp only [← Finset.sum_sub_distrib,Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _=_ := he

end AMSPhysical

#print axioms AMSPhysical.qRacahSeries_difference_regularized
