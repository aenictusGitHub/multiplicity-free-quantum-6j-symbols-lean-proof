import QRacahNewtonBasis
import QRacahSeriesCoefficients

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

/-- The standard terminating 4phi3 q-Racah expression in a multiplicative grid variable. -/
def qRacahSeries (Q A B C D : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∑ k∈Finset.range (n+1),qRacahCoefficient Q A B C D (Q^n) k*qRacahNewton Q (C*D) t k

theorem qRacahSeries_zero (Q A B C D t : ℝ) : qRacahSeries Q A B C D 0 t=1 := by
  simp only [qRacahSeries,Nat.zero_add,Finset.sum_range_one,qRacahCoefficient_zero,qRacahNewton_zero,mul_one]

/-- The terminating hypergeometric expression satisfies its q-Racah difference equation.
The proof uses only finite products, a polynomial operator certificate, and finite sums. -/
theorem qRacahSeries_difference (Q A B C D t : ℝ) (hQ : Q≠0) (ht : t≠0) (n : ℕ)
    (hreg : QRacahSeriesRegular Q A B C D n)
    (hd0 : 1-C*D*t^2≠0) (hd1 : 1-C*D*Q*t^2≠0) (hd2 : 1-C*D*Q^2*t^2≠0) :
    qRacahB Q A B C D t*(qRacahSeries Q A B C D n (Q*t)-qRacahSeries Q A B C D n t)+
      qRacahD Q A B C D t*(qRacahSeries Q A B C D n (t/Q)-qRacahSeries Q A B C D n t)=
      qRacahLambda Q A B (Q^n)*qRacahSeries Q A B C D n t := by
  have he := finite_bidiagonal_eigen n
    (qRacahCoefficient Q A B C D (Q^n)) (qRacahNewton Q (C*D) t)
    (fun k => qRacahB Q A B C D t*(qRacahNewton Q (C*D) (Q*t) k-qRacahNewton Q (C*D) t k)+
      qRacahD Q A B C D t*(qRacahNewton Q (C*D) (t/Q) k-qRacahNewton Q (C*D) t k))
    (fun k => qRacahLambda Q A B (Q^k)) (fun k => qRacahNu A B C D (Q^k)) (qRacahLambda Q A B (Q^n))
    (by simp only [qRacahNewton_zero,sub_self,mul_zero,add_zero,pow_zero,qRacahLambda,inv_one,zero_mul])
    (fun k hk => qRacahNewton_difference Q A B C D t hQ ht hd0 hd1 hd2 k)
    (fun k hk => qRacahCoefficient_eigen_step Q A B C D (Q^n) hQ (pow_ne_zero _ hQ) k
      (hreg k hk).1 (hreg k hk).2.1 (hreg k hk).2.2.1 (hreg k hk).2.2.2) rfl
  calc
    _=(∑ k∈Finset.range (n+1),qRacahCoefficient Q A B C D (Q^n) k*
        (qRacahB Q A B C D t*(qRacahNewton Q (C*D) (Q*t) k-qRacahNewton Q (C*D) t k)+
          qRacahD Q A B C D t*(qRacahNewton Q (C*D) (t/Q) k-qRacahNewton Q (C*D) t k))) := by
      unfold qRacahSeries
      simp only [← Finset.sum_sub_distrib,Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _=_ := he

end AMSPhysical

#print axioms AMSPhysical.qRacahSeries_difference
