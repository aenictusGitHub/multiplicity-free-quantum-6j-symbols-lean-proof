import SearsProductCancellation
import BasicFourTerm
import SaalschutzAdmissible

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

def searsWeight (Q a x e f : ℝ) (n k : ℕ) : ℝ :=
  qPochhammer Q (Q^(-(n:ℤ))) k*qPochhammer Q a k*qPochhammer Q x k*Q^k/
    (qPochhammer Q Q k*qPochhammer Q e k*qPochhammer Q f k)

def searsOuter (Q a b c d e f x : ℝ) (n j : ℕ) : ℝ :=
  qPochhammer Q (Q^(-(n:ℤ))) j*qPochhammer Q a j*
    qPochhammer Q (d/b) j*qPochhammer Q (d/c) j*(x*Q)^j/
      (qPochhammer Q Q j*qPochhammer Q d j*qPochhammer Q e j*qPochhammer Q f j)

theorem sears_cancellation_quotient (Q x : ℝ) (hQ : Q≠0) (hx : x≠0)
    (k j : ℕ) (hj : j≤k) (hQk : qPochhammer Q Q k≠0)
    (hQi : qPochhammer Q Q (k-j)≠0) (hD : qPochhammer Q (Q^(1-(k:ℤ))/x) j≠0) :
    qPochhammer Q (Q^(-(k:ℤ))) j*qPochhammer Q x k*Q^j/
      (qPochhammer Q Q k*qPochhammer Q (Q^(1-(k:ℤ))/x) j)=
      x^j*qPochhammer Q x (k-j)/qPochhammer Q Q (k-j) := by
  apply (div_eq_div_iff (mul_ne_zero hQk hD) hQi).mpr
  linear_combination sears_product_cancellation Q x hQ hx k j hj

/-- The summand identity after interchanging the two finite summations. -/
theorem sears_term_convolution (Q a b c d e f x : ℝ) (hQ : 0<Q) (hQ1 : Q≠1)
    (hx : x≠0) (n j i : ℕ) (hji : j+i≤n)
    (hd : qPochhammer Q d n≠0) (he : qPochhammer Q e n≠0)
    (hf : qPochhammer Q f n≠0)
    (hD : qPochhammer Q (Q^(1-((j+i:ℕ):ℤ))/x) j≠0) :
    searsWeight Q a x e f n (j+i)*
      basic3Term Q (d/b) (d/c) (Q^(j+i))⁻¹ d (Q^(1-((j+i:ℕ):ℤ))/x) j=
    searsOuter Q a b c d e f x n j*
      basic3Term Q (a*Q^j) x (Q^(n-j))⁻¹ (e*Q^j) (f*Q^j) i := by
  have hq0 := ne_of_gt hQ
  have hQk := qPochhammer_ne_zero Q Q (j+i) (fun k _ => baseQ_factor_nonzero Q hQ hQ1 k)
  have hQi := qPochhammer_ne_zero Q Q i (fun k _ => baseQ_factor_nonzero Q hQ hQ1 k)
  have hQj := qPochhammer_ne_zero Q Q j (fun k _ => baseQ_factor_nonzero Q hQ hQ1 k)
  have hdj := qPochhammer_prefix_ne_zero Q d n j hd (by omega)
  have hej := qPochhammer_prefix_ne_zero Q e n j he (by omega)
  have hfj := qPochhammer_prefix_ne_zero Q f n j hf (by omega)
  have hek := qPochhammer_prefix_ne_zero Q e n (j+i) he hji
  have hfk := qPochhammer_prefix_ne_zero Q f n (j+i) hf hji
  have heSplit := qPochhammer_add Q e j i
  have hfSplit := qPochhammer_add Q f j i
  have hei : qPochhammer Q (e*Q^j) i≠0 := by
    rw [heSplit] at hek
    exact (mul_ne_zero_iff.mp hek).2
  have hfi : qPochhammer Q (f*Q^j) i≠0 := by
    rw [hfSplit] at hfk
    exact (mul_ne_zero_iff.mp hfk).2
  have hc := sears_product_cancellation Q x hq0 hx (j+i) j (by omega)
  have hsub : j+i-j=i := by omega
  rw [hsub] at hc
  have hN : Q^(-(n:ℤ))*Q^j=(Q^(n-j))⁻¹ := by
    rw [← zpow_natCast Q j,← zpow_add₀ hq0,← zpow_natCast Q (n-j),← zpow_neg]
    congr 1
    omega
  have hkInv : (Q^(j+i))⁻¹=Q^(-((j+i:ℕ):ℤ)) := by rw [← zpow_natCast Q (j+i),zpow_neg]
  unfold searsWeight searsOuter basic3Term
  rw [hkInv,qPochhammer_add Q (Q^(-(n:ℤ))) j i,
    qPochhammer_add Q a j i,heSplit,hfSplit,hN,pow_add,mul_pow]
  simp only [mul_comm e (Q^j),mul_comm f (Q^j),one_div] at hei hfi ⊢
  field_simp [hQk,hQi,hQj,hdj,hej,hfj,hei,hfi,hD]
  linear_combination qPochhammer Q (Q^(-(n:ℤ))) j*qPochhammer Q (1/(Q^(n-j))) i*
    qPochhammer Q a j*qPochhammer Q (a*Q^j) i*qPochhammer Q (d/b) j*qPochhammer Q (d/c) j*hc

end AMSPhysical

#print axioms AMSPhysical.sears_term_convolution
