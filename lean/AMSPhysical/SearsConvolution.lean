import SearsTermConvolution
import TriangularSumReindex
import NormalizedSaalschutz

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

theorem qPochhammer_reflected_nonzero (Q a : ℝ) (hQ : Q≠0) (ha : a≠0)
    (n : ℕ) (h : qPochhammer Q a n≠0) : qPochhammer Q (Q^(1-(n:ℤ))/a) n≠0 := by
  rw [qPochhammer_reflection Q a hQ ha n] at h
  exact (mul_ne_zero_iff.mp h).2

theorem qPochhammer_suffix_nonzero (Q a : ℝ) (n j : ℕ) (hj : j≤n)
    (h : qPochhammer Q a n≠0) : qPochhammer Q (a*Q^j) (n-j)≠0 := by
  have he : n=j+(n-j) := by omega
  rw [he,qPochhammer_add] at h
  have hh : j+(n-j)-j=n-j := by omega
  exact (mul_ne_zero_iff.mp h).2

/-- The q-Pfaff summation inserted into a balanced 4phi3 transformation. -/
theorem sears_pfaff_insertion (Q b c d x : ℝ) (hQ : 0<Q) (hQ1 : Q≠1)
    (hb : b≠0) (hc : c≠0) (hd : d≠0) (hx : x≠0) (hrel : d*x=b*c)
    (k : ℕ) (hdP : qPochhammer Q d k≠0) (hxP : qPochhammer Q x k≠0) :
    (∑ j∈Finset.range (k+1),basic3Term Q (d/b) (d/c) (Q^k)⁻¹ d (Q^(1-(k:ℤ))/x) j)=
      qPochhammer Q b k*qPochhammer Q c k/(qPochhammer Q d k*qPochhammer Q x k) := by
  have hq0 := ne_of_gt hQ
  have hAB : (d/b)*(d/c)=d/x := by
    apply (eq_div_iff hx).mpr
    field_simp [hb,hc]
    linear_combination hrel
  have hD : (d/b)*(d/c)*Q/(d*Q^k)=Q^(1-(k:ℤ))/x := by
    rw [hAB,zpow_sub₀ hq0,zpow_one,zpow_natCast]
    field_simp [hd,hx,pow_ne_zero k hq0]
  have hProd : d/((d/b)*(d/c))=x := by rw [hAB];field_simp [hd,hx]
  have h₁ : d/(d/b)=b := by field_simp [hd,hb]
  have h₂ : d/(d/c)=c := by field_simp [hd,hc]
  have hDP := qPochhammer_reflected_nonzero Q x hq0 hx k hxP
  have hh := qPfaffSaalschutz_normalized Q (d/b) (d/c) d hQ hQ1
    (div_ne_zero hd hb) (div_ne_zero hd hc) hd k hdP (by rw [hD];exact hDP) (by rw [hProd];exact hxP)
  simpa only [hD,hProd,h₁,h₂] using hh

theorem sears_first_convolution (Q a b c d e f x : ℝ) (hQ : 0<Q) (hQ1 : Q≠1)
    (hb : b≠0) (hc : c≠0) (hd : d≠0) (hx : x≠0) (hrel : d*x=b*c)
    (n : ℕ) (hdP : qPochhammer Q d n≠0) (heP : qPochhammer Q e n≠0)
    (hfP : qPochhammer Q f n≠0) (hxP : qPochhammer Q x n≠0) :
    (∑ k∈Finset.range (n+1),basic4Term Q a b c (Q^(-(n:ℤ))) d e f k)=
      ∑ j∈Finset.range (n+1),searsOuter Q a b c d e f x n j*
        (∑ i∈Finset.range (n-j+1),basic3Term Q (a*Q^j) x (Q^(n-j))⁻¹ (e*Q^j) (f*Q^j) i) := by
  have hq0 := ne_of_gt hQ
  have hterm (k : ℕ) (hk : k≤n) :
      basic4Term Q a b c (Q^(-(n:ℤ))) d e f k=
        searsWeight Q a x e f n k*
          (∑ j∈Finset.range (k+1),basic3Term Q (d/b) (d/c) (Q^k)⁻¹ d (Q^(1-(k:ℤ))/x) j) := by
    have hdk := qPochhammer_prefix_ne_zero Q d n k hdP hk
    have hxk := qPochhammer_prefix_ne_zero Q x n k hxP hk
    rw [sears_pfaff_insertion Q b c d x hQ hQ1 hb hc hd hx hrel k hdk hxk]
    unfold basic4Term searsWeight
    have hQk := qPochhammer_ne_zero Q Q k (fun j _ => baseQ_factor_nonzero Q hQ hQ1 j)
    have hek := qPochhammer_prefix_ne_zero Q e n k heP hk
    have hfk := qPochhammer_prefix_ne_zero Q f n k hfP hk
    field_simp [hdk,hxk,hQk,hek,hfk]
  calc
    _ = ∑ k∈Finset.range (n+1),∑ j∈Finset.range (k+1),
        searsWeight Q a x e f n k*basic3Term Q (d/b) (d/c) (Q^k)⁻¹ d (Q^(1-(k:ℤ))/x) j := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hterm k (by have hh := Finset.mem_range.mp hk;omega),Finset.mul_sum]
    _ = ∑ j∈Finset.range (n+1),∑ i∈Finset.range (n-j+1),
        searsWeight Q a x e f n (j+i)*basic3Term Q (d/b) (d/c) (Q^(j+i))⁻¹ d (Q^(1-((j+i:ℕ):ℤ))/x) j :=
      sum_triangular_reindex n _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hji : j+i≤n := by have h₁ := Finset.mem_range.mp hj;have h₂ := Finset.mem_range.mp hi;omega
      have hxk := qPochhammer_prefix_ne_zero Q x n (j+i) hxP hji
      have hD := qPochhammer_reflected_nonzero Q x hq0 hx (j+i) hxk
      exact sears_term_convolution Q a b c d e f x hQ hQ1 hx n j i hji hdP heP hfP
        (qPochhammer_prefix_ne_zero Q _ (j+i) j hD (by omega))

end AMSPhysical

#print axioms AMSPhysical.sears_first_convolution
