import BasicHypergeometricTerm
import SaalschutzNormalizedParameters
import SaalschutzTelescopingAlgebra

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical

theorem saalschutzTerm_normalized (Q A B C : ℝ) (hQ : Q≠0) (n k : ℕ) :
    saalschutzTerm Q A B C n k=basic3Term Q A B (Q^n)⁻¹ C (A*B*Q/(C*Q^n)) k := by
  have hd : A*B*Q^(1-(n:ℤ))/C=A*B*Q/(C*Q^n) := by
    rw [zpow_sub₀ hQ,zpow_one,zpow_natCast]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  unfold saalschutzTerm basic3Term
  rw [zpow_neg,zpow_natCast,hd]

theorem saalschutzTerm_next_normalized (Q A B C : ℝ) (hQ : Q≠0) (n k : ℕ) :
    saalschutzTerm Q A B C (n+1) k=basic3Term Q A B (Q*Q^n)⁻¹ C (A*B/(C*Q^n)) k := by
  rw [saalschutzTerm_normalized Q A B C hQ,pow_succ']
  have hd : A*B*Q/(C*(Q*Q^n))=A*B/(C*Q^n) := by
    field_simp
  rw [hd]

theorem saalschutzTerm_prev_shifted (Q A B C : ℝ) (hQ : Q≠0) (n k : ℕ) :
    saalschutzTerm Q A B C n k=
      basic3Term Q A B ((Q*Q^n)⁻¹*Q) C ((A*B/(C*Q^n))*Q) k := by
  rw [saalschutzTerm_normalized Q A B C hQ]
  have hu : (Q*Q^n)⁻¹*Q=(Q^n)⁻¹ := by field_simp
  have hd : (A*B/(C*Q^n))*Q=A*B*Q/(C*Q^n) := by ring
  rw [hu,hd]

theorem saalschutzTerm_nshift (Q A B C : ℝ) (hQ : 0<Q) (hQ1 : Q≠1)
    (h : SaalschutzGeneric Q A B C) (n k : ℕ) :
    saalschutzTerm Q A B C n k=saalschutzTerm Q A B C (n+1) k*
      saalschutzNratio A B C Q (Q^n) (Q^k) := by
  have hQP : qPochhammer Q Q k≠0 := qPochhammer_ne_zero _ _ _ (fun i _ => baseQ_factor_nonzero Q hQ hQ1 i)
  have hCP : qPochhammer Q C k≠0 := qPochhammer_ne_zero _ _ _ (fun i _ => h.C_factor (ne_of_gt hQ) i)
  have hDP : qPochhammer Q (A*B/(C*Q^n)) k≠0 := qPochhammer_ne_zero _ _ _
    (fun i _ => h.D_factor (ne_of_gt hQ) n i)
  have hD : 1-A*B/(C*Q^n)≠0 := by simpa only [pow_zero,mul_one] using h.D_factor (ne_of_gt hQ) n 0
  rw [saalschutzTerm_prev_shifted Q A B C (ne_of_gt hQ),saalschutzTerm_next_normalized Q A B C (ne_of_gt hQ)]
  rw [basic3Term_shift Q A B ((Q*Q^n)⁻¹) C (A*B/(C*Q^n)) k
    (saalschutz_U_ne Q hQ hQ1 n) hD hQP hCP hDP]
  congr 1
  unfold saalschutzNratio
  have hN := pow_ne_zero n (ne_of_gt hQ)
  have hQN := saalschutz_QN_ne Q hQ hQ1 n
  have hX := h.CN_ABx_ne (ne_of_gt hQ) n k
  field_simp [h.ne_zero]

theorem saalschutzTerm_kshift (Q A B C : ℝ) (hQ : 0<Q) (hQ1 : Q≠1)
    (h : SaalschutzGeneric Q A B C) (n k : ℕ) :
    saalschutzTerm Q A B C (n+1) (k+1)=saalschutzTerm Q A B C (n+1) k*
      saalschutzKratio A B C Q (Q^n) (Q^k) := by
  rw [saalschutzTerm_next_normalized Q A B C (ne_of_gt hQ),
    saalschutzTerm_next_normalized Q A B C (ne_of_gt hQ),basic3Term_succ]
  congr 1
  unfold saalschutzKratio
  have hN := pow_ne_zero n (ne_of_gt hQ)
  have hQx := baseQ_factor_nonzero Q hQ hQ1 k
  have hCx := h.C_factor (ne_of_gt hQ) k
  have hX := h.CN_ABx_ne (ne_of_gt hQ) n k
  field_simp [h.ne_zero]

end AMSPhysical

#print axioms AMSPhysical.saalschutzTerm_nshift
#print axioms AMSPhysical.saalschutzTerm_kshift
