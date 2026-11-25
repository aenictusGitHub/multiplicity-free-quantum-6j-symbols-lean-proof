import QRacahLowerEndpoint

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem qRacahSeries_upper_A_reduction (Q A B C D : ℝ) (hC : C≠0) (hD : D≠0) (n : ℕ)
    (hAQ : qPochhammer Q (A*Q) n≠0) :
    qRacahSeries Q A B C D n (A/(C*D))=
      ∑ k∈Finset.range (n+1),basic3Term Q (A*B*Q*Q^n) (C*D/A) (Q^n)⁻¹ (B*D*Q) (C*Q) k := by
  unfold qRacahSeries
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k≤n := by have hh := Finset.mem_range.mp hk;omega
  have harg : C*D*Q*(A/(C*D))=A*Q := by field_simp
  rw [qRacahTerm_basic4,harg,inv_div,
    basic4Term_cancel_first Q (A*B*Q*Q^n) (C*D/A) (Q^n)⁻¹ (A*Q) (B*D*Q) (C*Q) k
      (qPochhammer_prefix_ne_zero Q (A*Q) n k hAQ hkn)]

theorem qRacahSeries_upper_A_endpoint (Q A B C D : ℝ) (hQ : 0<Q) (hQ1 : Q≠1)
    (hA : A≠0) (hB : B≠0) (hC : C≠0) (hD : D≠0) (n : ℕ)
    (hAQ : qPochhammer Q (A*Q) n≠0) (hBD : qPochhammer Q (B*D*Q) n≠0)
    (hCQ : qPochhammer Q (C*Q) n≠0) (hCN : qPochhammer Q (1/(C*Q^n)) n≠0) :
    qRacahSeries Q A B C D n (A/(C*D))=
      qPochhammer Q (D/(A*Q^n)) n*qPochhammer Q (A*B*Q/C) n/
        (qPochhammer Q (B*D*Q) n*qPochhammer Q (1/(C*Q^n)) n) := by
  have hQN := pow_ne_zero n (ne_of_gt hQ)
  have hd : (A*B*Q*Q^n)*(C*D/A)*Q/((B*D*Q)*Q^n)=C*Q := by
    field_simp [hA,hB,hD,ne_of_gt hQ,hQN]
  have hp : (B*D*Q)/((A*B*Q*Q^n)*(C*D/A))=1/(C*Q^n) := by
    field_simp [hA,hB,hC,hD,ne_of_gt hQ,hQN]
  have hn1 : (B*D*Q)/(A*B*Q*Q^n)=D/(A*Q^n) := by
    field_simp [hA,hB,ne_of_gt hQ,hQN]
  have hn2 : (B*D*Q)/(C*D/A)=A*B*Q/C := by
    field_simp [hA,hC,hD]
  have hs := qPfaffSaalschutz_normalized Q (A*B*Q*Q^n) (C*D/A) (B*D*Q) hQ hQ1
    (mul_ne_zero (mul_ne_zero (mul_ne_zero hA hB) (ne_of_gt hQ)) hQN)
    (div_ne_zero (mul_ne_zero hC hD) hA) (mul_ne_zero (mul_ne_zero hB hD) (ne_of_gt hQ)) n hBD
    (by rw [hd];exact hCQ) (by rw [hp];exact hCN)
  rw [hd,hp,hn1,hn2] at hs
  rw [qRacahSeries_upper_A_reduction Q A B C D hC hD n hAQ]
  exact hs

theorem qRacahSeries_upper_D_reduction (Q A B C D : ℝ) (hD : D≠0) (n : ℕ)
    (hCQ : qPochhammer Q (C*Q) n≠0) :
    qRacahSeries Q A B C D n D⁻¹=
      ∑ k∈Finset.range (n+1),basic3Term Q (A*B*Q*Q^n) D (Q^n)⁻¹ (A*Q) (B*D*Q) k := by
  unfold qRacahSeries
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k≤n := by have hh := Finset.mem_range.mp hk;omega
  have harg : C*D*Q*D⁻¹=C*Q := by field_simp
  rw [qRacahTerm_basic4,harg,inv_inv,
    basic4Term_cancel_last Q (A*B*Q*Q^n) D (Q^n)⁻¹ (A*Q) (B*D*Q) (C*Q) k
      (qPochhammer_prefix_ne_zero Q (C*Q) n k hCQ hkn)]

theorem qRacahSeries_upper_D_endpoint (Q A B C D : ℝ) (hQ : 0<Q) (hQ1 : Q≠1)
    (hA : A≠0) (hB : B≠0) (hD : D≠0) (n : ℕ)
    (hAQ : qPochhammer Q (A*Q) n≠0) (hBD : qPochhammer Q (B*D*Q) n≠0)
    (hCQ : qPochhammer Q (C*Q) n≠0) (hBDN : qPochhammer Q (1/(B*D*Q^n)) n≠0) :
    qRacahSeries Q A B C D n D⁻¹=
      qPochhammer Q (1/(B*Q^n)) n*qPochhammer Q (A*Q/D) n/
        (qPochhammer Q (A*Q) n*qPochhammer Q (1/(B*D*Q^n)) n) := by
  have hQN := pow_ne_zero n (ne_of_gt hQ)
  have hd : (A*B*Q*Q^n)*D*Q/((A*Q)*Q^n)=B*D*Q := by
    field_simp [hA,ne_of_gt hQ,hQN]
  have hp : (A*Q)/((A*B*Q*Q^n)*D)=1/(B*D*Q^n) := by
    field_simp [hA,hB,hD,ne_of_gt hQ,hQN]
  have hn1 : (A*Q)/(A*B*Q*Q^n)=1/(B*Q^n) := by
    field_simp [hA,hB,ne_of_gt hQ,hQN]
  have hs := qPfaffSaalschutz_normalized Q (A*B*Q*Q^n) D (A*Q) hQ hQ1
    (mul_ne_zero (mul_ne_zero (mul_ne_zero hA hB) (ne_of_gt hQ)) hQN)
    hD (mul_ne_zero hA (ne_of_gt hQ)) n hAQ
    (by rw [hd];exact hBD) (by rw [hp];exact hBDN)
  rw [hd,hp,hn1] at hs
  rw [qRacahSeries_upper_D_reduction Q A B C D hD n hCQ]
  exact hs

end AMSPhysical

#print axioms AMSPhysical.qRacahSeries_upper_A_endpoint
#print axioms AMSPhysical.qRacahSeries_upper_D_endpoint
