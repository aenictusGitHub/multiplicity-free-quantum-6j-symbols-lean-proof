import QRacahNewtonAlgebra

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

/-- The two degree-dependent upper factors and four lower factors of the terminating 4phi3. -/
def qRacahCoefficient (Q A B C D N : ℝ) (k : ℕ) : ℝ :=
  qPochhammer Q N⁻¹ k*qPochhammer Q (A*B*Q*N) k*Q^k/
    (qPochhammer Q Q k*qPochhammer Q (A*Q) k*qPochhammer Q (B*D*Q) k*qPochhammer Q (C*Q) k)

def QRacahSeriesRegular (Q A B C D : ℝ) (n : ℕ) : Prop :=
  ∀ k,k<n → (1-Q*Q^k≠0) ∧ (1-A*Q*Q^k≠0) ∧ (1-B*D*Q*Q^k≠0) ∧ (1-C*Q*Q^k≠0)

theorem qRacahCoefficient_zero (Q A B C D N : ℝ) : qRacahCoefficient Q A B C D N 0=1 := by
  simp only [qRacahCoefficient,qPochhammer_zero,pow_zero,mul_one,div_one]

theorem qRacahCoefficient_succ (Q A B C D N : ℝ) (k : ℕ) :
    qRacahCoefficient Q A B C D N (k+1)=qRacahCoefficient Q A B C D N k*
      (Q*(1-N⁻¹*Q^k)*(1-A*B*Q*N*Q^k)/
        ((1-Q*Q^k)*(1-A*Q*Q^k)*(1-B*D*Q*Q^k)*(1-C*Q*Q^k))) := by
  unfold qRacahCoefficient
  simp only [qPochhammer_succ,pow_succ',div_eq_mul_inv,mul_inv_rev]
  ring

theorem qRacah_coefficient_algebra (Q A B C D N K : ℝ) (hQ : Q≠0) (hN : N≠0) (hK : K≠0)
    (hd0 : 1-Q*K≠0) (hd1 : 1-A*Q*K≠0) (hd2 : 1-B*D*Q*K≠0) (hd3 : 1-C*Q*K≠0) :
    (Q*(1-N⁻¹*K)*(1-A*B*Q*N*K)/((1-Q*K)*(1-A*Q*K)*(1-B*D*Q*K)*(1-C*Q*K)))*
      qRacahNu A B C D (Q*K)=qRacahLambda Q A B N-qRacahLambda Q A B K := by
  let H := (1-A*Q*K)*(1-B*D*Q*K)*(1-C*Q*K)
  have hH : H≠0 := mul_ne_zero (mul_ne_zero hd1 hd2) hd3
  have hnu : qRacahNu A B C D (Q*K)=(1-(Q*K)⁻¹)*H := by
    unfold qRacahNu H
    ring
  have hden : (1-Q*K)*(1-A*Q*K)*(1-B*D*Q*K)*(1-C*Q*K)=(1-Q*K)*H := by
    unfold H
    ring
  rw [hnu,hden]
  calc
    _=(Q*(1-N⁻¹*K)*(1-A*B*Q*N*K)*(1-(Q*K)⁻¹)*H)/((1-Q*K)*H) := by
      rw [div_mul_eq_mul_div]
      congr 1
      ring
    _=(Q*(1-N⁻¹*K)*(1-A*B*Q*N*K)*(1-(Q*K)⁻¹))/(1-Q*K) := mul_div_mul_right _ _ hH
    _=_ := by
      unfold qRacahLambda
      have hn0 : 1-K*Q≠0 := by convert hd0 using 1 <;> ring
      field_simp [hQ,hN,hK,hd0,hn0] <;> ring


theorem qRacahCoefficient_eigen_step (Q A B C D N : ℝ) (hQ : Q≠0) (hN : N≠0) (k : ℕ)
    (hd0 : 1-Q*Q^k≠0) (hd1 : 1-A*Q*Q^k≠0) (hd2 : 1-B*D*Q*Q^k≠0) (hd3 : 1-C*Q*Q^k≠0) :
    qRacahCoefficient Q A B C D N (k+1)*qRacahNu A B C D (Q^(k+1))=
      (qRacahLambda Q A B N-qRacahLambda Q A B (Q^k))*qRacahCoefficient Q A B C D N k := by
  rw [qRacahCoefficient_succ,pow_succ' Q k,mul_assoc,
    qRacah_coefficient_algebra Q A B C D N (Q^k) hQ hN (pow_ne_zero _ hQ) hd0 hd1 hd2 hd3,mul_comm]

/-- A finite bidiagonal eigenvector calculation, with no linear independence assumption. -/
theorem finite_bidiagonal_eigen (n : ℕ) (c f d lam nu : ℕ → ℝ) (L : ℝ)
    (h0 : d 0=lam 0*f 0) (hstep : ∀ k,k<n → d (k+1)=lam (k+1)*f (k+1)+nu (k+1)*f k)
    (hc : ∀ k,k<n → c (k+1)*nu (k+1)=(L-lam k)*c k)
    (hn : lam n=L) :
    (∑ k∈Finset.range (n+1),c k*d k)=L*(∑ k∈Finset.range (n+1),c k*f k) := by
  have aux : ∀ m,m≤n → (∑ k∈Finset.range (m+1),c k*d k)=
      L*(∑ k∈Finset.range (m+1),c k*f k)+(lam m-L)*c m*f m := by
    intro m
    induction m with
    | zero =>
      intro hm
      simp only [Nat.zero_add,Finset.sum_range_one]
      rw [h0]
      ring
    | succ m ih =>
      intro hm
      rw [Finset.sum_range_succ (fun k => c k*d k) (m+1),
        Finset.sum_range_succ (fun k => c k*f k) (m+1),ih (by omega),hstep m (by omega)]
      have hh := hc m (by omega)
      linear_combination f m*hh
  have he := aux n (le_refl n)
  rw [hn,sub_self,zero_mul,zero_mul,add_zero] at he
  exact he

end AMSPhysical

#print axioms AMSPhysical.qRacahCoefficient_eigen_step
#print axioms AMSPhysical.finite_bidiagonal_eigen
