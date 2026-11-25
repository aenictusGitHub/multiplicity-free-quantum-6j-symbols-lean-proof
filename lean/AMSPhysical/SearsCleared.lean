import SearsSecondSum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

def searsClearedTerm (Q a b c d e f x : ℝ) (n j : ℕ) : ℝ :=
  qPochhammer Q (Q^(-(n:ℤ))) j*qPochhammer Q a j*qPochhammer Q (d/b) j*qPochhammer Q (d/c) j/
    (qPochhammer Q Q j*qPochhammer Q d j)*
      a^(n-j)*x^j*Q^(j*(n-j+1))*qPochhammer Q (e/a) (n-j)*qPochhammer Q (f/a) (n-j)

theorem sears_cleared_term (Q a b c d e f x : ℝ) (hQ : 0<Q) (hQ1 : Q≠1)
    (ha : a≠0) (he : e≠0) (hf : f≠0) (hx : x≠0) (n j : ℕ) (hj : j≤n)
    (hbal : e*f=a*x*Q^(1-(n:ℤ)))
    (hdP : qPochhammer Q d n≠0) (heP : qPochhammer Q e n≠0) (hfP : qPochhammer Q f n≠0) :
    searsOuter Q a b c d e f x n j*
      (∑ i∈Finset.range (n-j+1),basic3Term Q (a*Q^j) x (Q^(n-j))⁻¹ (e*Q^j) (f*Q^j) i)*
      qPochhammer Q e n*qPochhammer Q f n=searsClearedTerm Q a b c d e f x n j := by
  have hq0 := ne_of_gt hQ
  have hQj := qPochhammer_ne_zero Q Q j (fun k _ => baseQ_factor_nonzero Q hQ hQ1 k)
  have hdj := qPochhammer_prefix_ne_zero Q d n j hdP hj
  have hej := qPochhammer_prefix_ne_zero Q e n j heP hj
  have hfj := qPochhammer_prefix_ne_zero Q f n j hfP hj
  have heSplit : qPochhammer Q e n=qPochhammer Q e j*qPochhammer Q (e*Q^j) (n-j) := by
    have hn : n=j+(n-j) := by omega
    conv_lhs => rw [hn,qPochhammer_add]
  have hfSplit : qPochhammer Q f n=qPochhammer Q f j*qPochhammer Q (f*Q^j) (n-j) := by
    have hn : n=j+(n-j) := by omega
    conv_lhs => rw [hn,qPochhammer_add]
  have hsum := sears_second_sum_cleared Q a e f x hQ hQ1 ha he hf hx n j hj hbal heP hfP
  have hphase : (x*Q)^j*Q^(j*(n-j))=x^j*Q^(j*(n-j+1)) := by
    rw [mul_pow,mul_assoc,← pow_add]
    congr 2
    ring
  calc
    _ = (qPochhammer Q (Q^(-(n:ℤ))) j*qPochhammer Q a j*qPochhammer Q (d/b) j*qPochhammer Q (d/c) j/
        (qPochhammer Q Q j*qPochhammer Q d j))*(x*Q)^j*
      ((∑ i∈Finset.range (n-j+1),basic3Term Q (a*Q^j) x (Q^(n-j))⁻¹ (e*Q^j) (f*Q^j) i)*
        qPochhammer Q (e*Q^j) (n-j)*qPochhammer Q (f*Q^j) (n-j)) := by
      unfold searsOuter
      rw [heSplit,hfSplit]
      field_simp [hQj,hdj,hej,hfj]
    _ = _ := by
      rw [hsum]
      unfold searsClearedTerm
      linear_combination
        (qPochhammer Q (Q^(-(n:ℤ))) j*qPochhammer Q a j*qPochhammer Q (d/b) j*qPochhammer Q (d/c) j/
          (qPochhammer Q Q j*qPochhammer Q d j))*a^(n-j)*
          qPochhammer Q (e/a) (n-j)*qPochhammer Q (f/a) (n-j)*hphase

/-- Terminating balanced Sears transformation with all transformed lower
Pochhammers cleared. Unlike a literal transformed 4phi3, its right side
retains the exact cancellation information at physical boundary labels. -/
theorem qSears_cleared_generic (Q a b c d e f x : ℝ) (hQ : 0<Q) (hQ1 : Q≠1)
    (ha : a≠0) (hb : b≠0) (hc : c≠0) (hd : d≠0) (he : e≠0) (hf : f≠0) (hx : x≠0)
    (hrel : d*x=b*c) (n : ℕ) (hbal : e*f=a*x*Q^(1-(n:ℤ)))
    (hdP : qPochhammer Q d n≠0) (heP : qPochhammer Q e n≠0)
    (hfP : qPochhammer Q f n≠0) (hxP : qPochhammer Q x n≠0) :
    (∑ k∈Finset.range (n+1),basic4Term Q a b c (Q^(-(n:ℤ))) d e f k)*
      qPochhammer Q e n*qPochhammer Q f n=
      ∑ j∈Finset.range (n+1),searsClearedTerm Q a b c d e f x n j := by
  rw [sears_first_convolution Q a b c d e f x hQ hQ1 hb hc hd hx hrel n hdP heP hfP hxP,
    Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  exact sears_cleared_term Q a b c d e f x hQ hQ1 ha he hf hx n j
    (by have hh := Finset.mem_range.mp hj;omega) hbal hdP heP hfP

end AMSPhysical

#print axioms AMSPhysical.qSears_cleared_generic
