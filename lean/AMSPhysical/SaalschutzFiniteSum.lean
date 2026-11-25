import SaalschutzTermRecurrences

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical

def saalschutzG (Q A B C : ℝ) (n k : ℕ) : ℝ :=
  saalschutzFlux Q C (Q^n) (Q^k)*saalschutzTerm Q A B C (n+1) k

theorem saalschutzTerm_telescoping (Q A B C : ℝ) (hQ : 0<Q) (hQ1 : Q≠1)
    (h : SaalschutzGeneric Q A B C) (n k : ℕ) :
    saalschutzTerm Q A B C (n+1) k-saalschutzRatio A B C (Q^n)*saalschutzTerm Q A B C n k=
      saalschutzG Q A B C n (k+1)-saalschutzG Q A B C n k := by
  unfold saalschutzG
  rw [saalschutzTerm_nshift Q A B C hQ hQ1 h n k,
    saalschutzTerm_kshift Q A B C hQ hQ1 h n k,pow_succ']
  exact saalschutz_telescoping_algebra A B C Q (Q^n) (Q^k) (saalschutzTerm Q A B C (n+1) k)
    (ne_of_gt hQ) (pow_ne_zero _ (ne_of_gt hQ)) (pow_ne_zero _ (ne_of_gt hQ))
    (h.CN_ne (ne_of_gt hQ) n) (saalschutz_QN_ne Q hQ hQ1 n) (h.AB_CN_ne (ne_of_gt hQ) n)
    (h.CN_ABx_ne (ne_of_gt hQ) n k) (baseQ_factor_nonzero Q hQ hQ1 k) (h.C_factor (ne_of_gt hQ) k)

theorem saalschutzG_zero (Q A B C : ℝ) (n : ℕ) : saalschutzG Q A B C n 0=0 := by
  simp only [saalschutzG,saalschutzFlux,pow_zero,sub_self,mul_zero,zero_mul,zero_div]

theorem saalschutzG_terminal (Q A B C : ℝ) (hQ : Q≠0) (n : ℕ) : saalschutzG Q A B C n (n+2)=0 := by
  rw [saalschutzG,saalschutzTerm_terminates Q A B C hQ (n+1) (n+2) (by omega),mul_zero]

theorem sum_discrete_flux (f : ℕ → ℝ) (n : ℕ) :
    (∑ k∈Finset.range n,(f (k+1)-f k))=f n-f 0 := by
  induction n with
  | zero => simp only [Finset.range_zero,Finset.sum_empty,sub_self]
  | succ n ih => rw [Finset.sum_range_succ,ih];ring

theorem saalschutzSum_step (Q A B C : ℝ) (hQ : 0<Q) (hQ1 : Q≠1)
    (h : SaalschutzGeneric Q A B C) (n : ℕ) :
    saalschutzSum Q A B C (n+1)=saalschutzRatio A B C (Q^n)*saalschutzSum Q A B C n := by
  have he : (∑ k∈Finset.range (n+2),
      (saalschutzTerm Q A B C (n+1) k-saalschutzRatio A B C (Q^n)*saalschutzTerm Q A B C n k))=
      ∑ k∈Finset.range (n+2),(saalschutzG Q A B C n (k+1)-saalschutzG Q A B C n k) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact saalschutzTerm_telescoping Q A B C hQ hQ1 h n k
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,sum_discrete_flux,
    saalschutzG_terminal Q A B C (ne_of_gt hQ),saalschutzG_zero,sub_self] at he
  have hold : (∑ k∈Finset.range (n+2),saalschutzTerm Q A B C n k)=saalschutzSum Q A B C n := by
    rw [Finset.sum_range_succ,
      saalschutzTerm_terminates Q A B C (ne_of_gt hQ) n (n+1) (by omega),add_zero]
    rfl
  rw [hold] at he
  exact sub_eq_zero.mp he

theorem saalschutzProduct_step (Q A B C : ℝ) (hQ : 0<Q)
    (hA : A≠0) (hB : B≠0) (h : SaalschutzGeneric Q A B C) (n : ℕ) :
    saalschutzProduct Q A B C (n+1)=saalschutzRatio A B C (Q^n)*saalschutzProduct Q A B C n := by
  have hr : ((1-C/A*Q^n)*(1-C/B*Q^n)/((1-C*Q^n)*(1-C/(A*B)*Q^n)))=
      saalschutzRatio A B C (Q^n) := by
    unfold saalschutzRatio
    have hCN : 1-C*Q^n≠0 := h.C_factor (ne_of_gt hQ) n
    have hAB := h.AB_CN_ne (ne_of_gt hQ) n
    field_simp
  rw [← hr]
  unfold saalschutzProduct
  simp only [qPochhammer_succ,div_eq_mul_inv,mul_inv_rev]
  ring

/-- Terminating balanced 3phi2 summation, proved by an explicit telescoping certificate. -/
theorem qPfaffSaalschutz_generic (Q A B C : ℝ) (hQ : 0<Q) (hQ1 : Q≠1)
    (hA : A≠0) (hB : B≠0) (h : SaalschutzGeneric Q A B C) (n : ℕ) :
    saalschutzSum Q A B C n=saalschutzProduct Q A B C n := by
  induction n with
  | zero => simp only [saalschutzSum,Nat.zero_add,Finset.sum_range_one,saalschutzTerm_zero,
      saalschutzProduct,qPochhammer_zero,one_mul,div_one]
  | succ n ih => rw [saalschutzSum_step Q A B C hQ hQ1 h,ih,saalschutzProduct_step Q A B C hQ hA hB h]

end AMSPhysical

#print axioms AMSPhysical.qPfaffSaalschutz_generic
