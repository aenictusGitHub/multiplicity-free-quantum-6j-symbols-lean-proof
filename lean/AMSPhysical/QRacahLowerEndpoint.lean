import BasicFourTerm
import NormalizedSaalschutz

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

/-- At the lower physical endpoint one upper factor cancels a lower factor. -/
theorem qRacahSeries_lower_reduction (Q A B C D : ℝ) (hC : C≠0) (n : ℕ)
    (hBD : qPochhammer Q (B*D*Q) n≠0) :
    qRacahSeries Q A B C D n (B/C)=
      ∑ k∈Finset.range (n+1),basic3Term Q (A*B*Q*Q^n) (C/B) (Q^n)⁻¹ (A*Q) (C*Q) k := by
  unfold qRacahSeries
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k≤n := by have hh := Finset.mem_range.mp hk;omega
  have harg : C*D*Q*(B/C)=B*D*Q := by field_simp
  rw [qRacahTerm_basic4,harg,inv_div,
    basic4Term_cancel_middle Q (A*B*Q*Q^n) (C/B) (Q^n)⁻¹ (A*Q) (B*D*Q) (C*Q) k
      (qPochhammer_prefix_ne_zero Q (B*D*Q) n k hBD hkn)]

/-- Closed q-Pfaff-Saalschutz evaluation of the lower q-Racah endpoint. -/
theorem qRacahSeries_lower_endpoint (Q A B C D : ℝ) (hQ : 0<Q) (hQ1 : Q≠1)
    (hA : A≠0) (hB : B≠0) (hC : C≠0) (n : ℕ)
    (hAQ : qPochhammer Q (A*Q) n≠0) (hBD : qPochhammer Q (B*D*Q) n≠0)
    (hCQ : qPochhammer Q (C*Q) n≠0) (hCN : qPochhammer Q (1/(C*Q^n)) n≠0) :
    qRacahSeries Q A B C D n (B/C)=
      qPochhammer Q (1/(B*Q^n)) n*qPochhammer Q (A*B*Q/C) n/
        (qPochhammer Q (A*Q) n*qPochhammer Q (1/(C*Q^n)) n) := by
  have hQN := pow_ne_zero n (ne_of_gt hQ)
  have hd : (A*B*Q*Q^n)*(C/B)*Q/((A*Q)*Q^n)=C*Q := by
    field_simp [hA,hB,ne_of_gt hQ,hQN]
  have hp : (A*Q)/((A*B*Q*Q^n)*(C/B))=1/(C*Q^n) := by
    field_simp [hA,hB,hC,ne_of_gt hQ,hQN]
  have hn1 : (A*Q)/(A*B*Q*Q^n)=1/(B*Q^n) := by
    field_simp [hA,hB,ne_of_gt hQ,hQN]
  have hn2 : (A*Q)/(C/B)=A*B*Q/C := by
    field_simp [hB,hC]
  have hs := qPfaffSaalschutz_normalized Q (A*B*Q*Q^n) (C/B) (A*Q) hQ hQ1
    (mul_ne_zero (mul_ne_zero (mul_ne_zero hA hB) (ne_of_gt hQ)) hQN)
    (div_ne_zero hC hB) (mul_ne_zero hA (ne_of_gt hQ)) n hAQ
    (by rw [hd];exact hCQ) (by rw [hp];exact hCN)
  rw [hd,hp,hn1,hn2] at hs
  rw [qRacahSeries_lower_reduction Q A B C D hC n hBD]
  exact hs

end AMSPhysical

#print axioms AMSPhysical.qRacahSeries_lower_endpoint
