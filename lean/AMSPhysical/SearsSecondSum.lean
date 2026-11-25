import SearsConvolution

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

theorem qPfaffSaalschutz_normalized_cleared (Q A B C : ℝ) (hQ : 0<Q) (hQ1 : Q≠1)
    (hA : A≠0) (hB : B≠0) (hC : C≠0) (n : ℕ)
    (hCP : qPochhammer Q C n≠0) (hDP : qPochhammer Q (A*B*Q/(C*Q^n)) n≠0) :
    (∑ k∈Finset.range (n+1),basic3Term Q A B (Q^n)⁻¹ C (A*B*Q/(C*Q^n)) k)*
      qPochhammer Q C n*qPochhammer Q (C/(A*B)) n=
      qPochhammer Q (C/A) n*qPochhammer Q (C/B) n := by
  have hD : A*B*Q^(1-(n:ℤ))/C=A*B*Q/(C*Q^n) := by
    rw [zpow_sub₀ (ne_of_gt hQ),zpow_one,zpow_natCast]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have h := qPfaffSaalschutz_cleared Q A B C hQ hQ1 hA hB hC n hCP (by rw [hD];exact hDP)
  unfold saalschutzSum at h
  simp only [saalschutzTerm_normalized Q A B C (ne_of_gt hQ)] at h
  exact h

/-- The inner sum is evaluated in a form that retains all zero factors;
there is no hypothesis that the Saalschutz product denominator is nonzero. -/
theorem sears_second_sum_cleared (Q a e f x : ℝ) (hQ : 0<Q) (hQ1 : Q≠1)
    (ha : a≠0) (he : e≠0) (hf : f≠0) (hx : x≠0) (n j : ℕ) (hj : j≤n)
    (hbal : e*f=a*x*Q^(1-(n:ℤ)))
    (heP : qPochhammer Q e n≠0) (hfP : qPochhammer Q f n≠0) :
    (∑ i∈Finset.range (n-j+1),basic3Term Q (a*Q^j) x (Q^(n-j))⁻¹ (e*Q^j) (f*Q^j) i)*
      qPochhammer Q (e*Q^j) (n-j)*qPochhammer Q (f*Q^j) (n-j)=
      a^(n-j)*Q^(j*(n-j))*qPochhammer Q (e/a) (n-j)*qPochhammer Q (f/a) (n-j) := by
  have hq0 := ne_of_gt hQ
  have hQj := pow_ne_zero j hq0
  have hphase : Q^(1-((n-j:ℕ):ℤ))=Q^(1-(n:ℤ))*Q^j := by
    rw [← zpow_natCast Q j,← zpow_add₀ hq0]
    congr 1
    omega
  have hD : (a*Q^j)*x*Q/((e*Q^j)*Q^(n-j))=f*Q^j := by
    have hp : Q/(Q^(n-j))=Q^(1-(n:ℤ))*Q^j := by
      rw [← hphase,zpow_sub₀ hq0,zpow_one,zpow_natCast]
    calc
      _ = a*x*(Q/(Q^(n-j)))/e := by field_simp [he,hQj,pow_ne_zero (n-j) hq0]
      _ = f*Q^j := by rw [hp];field_simp [he];linear_combination -hbal
  have hCA : (e*Q^j)/(a*Q^j)=e/a := by field_simp [ha,hQj]
  have hCAB : (e*Q^j)/((a*Q^j)*x)=e/(a*x) := by field_simp [ha,hx,hQj]
  have hCP := qPochhammer_suffix_nonzero Q e n j hj heP
  have hFP := qPochhammer_suffix_nonzero Q f n j hj hfP
  have hp := qPfaffSaalschutz_normalized_cleared Q (a*Q^j) x (e*Q^j) hQ hQ1
    (mul_ne_zero ha hQj) hx (mul_ne_zero he hQj) (n-j) hCP (by rw [hD];exact hFP)
  simp only [hD,hCA,hCAB] at hp
  have hy : Q^(1-((n-j:ℕ):ℤ))/(f*Q^j)=e/(a*x) := by
    rw [hphase]
    field_simp [hf,hQj,ha,hx]
    linear_combination -hbal
  have hz : Q^(1-((n-j:ℕ):ℤ))/(f/a)=(e*Q^j)/x := by
    rw [hphase]
    field_simp [hf,ha,hx]
    linear_combination -hbal
  have hrF := qPochhammer_reflection Q (f*Q^j) hq0 (mul_ne_zero hf hQj) (n-j)
  have hrFA := qPochhammer_reflection Q (f/a) hq0 (div_ne_zero hf ha) (n-j)
  rw [hy] at hrF
  rw [hz] at hrFA
  have hc : (-(f*Q^j))^(n-j)=a^(n-j)*Q^(j*(n-j))*(-(f/a))^(n-j) := by
    rw [pow_mul,← mul_pow,← mul_pow]
    congr 1
    field_simp [ha]
  rw [hrF]
  calc
    _ = ((-(f*Q^j))^(n-j)*Q^((n-j).choose 2))*
      ((∑ i∈Finset.range (n-j+1),basic3Term Q (a*Q^j) x (Q^(n-j))⁻¹ (e*Q^j) (f*Q^j) i)*
        qPochhammer Q (e*Q^j) (n-j)*qPochhammer Q (e/(a*x)) (n-j)) := by ring
    _ = _ := by rw [hp,hc,hrFA];ring

end AMSPhysical

#print axioms AMSPhysical.sears_second_sum_cleared
