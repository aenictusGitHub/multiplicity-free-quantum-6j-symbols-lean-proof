import FixedDegrees

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical
open MvPolynomial

variable {K : Type*} [Field K]

def eulerFamily (n : ℕ) (a : Fin 4) (p : PN K n) : PN K n :=
  ∑ i,X (a,i)*pderiv (a,i) p

theorem eulerFamily_add (n : ℕ) (a : Fin 4) (p q : PN K n) :
    eulerFamily n a (p+q)=eulerFamily n a p+eulerFamily n a q := by
  simp [eulerFamily,mul_add,Finset.sum_add_distrib]

theorem eulerFamily_smul (n : ℕ) (a : Fin 4) (c : K) (p : PN K n) :
    eulerFamily n a (c • p)=c • eulerFamily n a p := by
  simp [eulerFamily,mul_smul_comm,Finset.smul_sum]

theorem eulerFamily_monomial (n : ℕ) (a : Fin 4) (m : Fin 4×Fin n →₀ ℕ) (c : K) :
    eulerFamily n a (monomial m c)=(∑ i : Fin n,m (a,i)) • monomial m c := by
  simp only [eulerFamily,X_mul_pderiv_monomial]
  rw [Finset.sum_smul]

theorem coeff_eulerFamily (n : ℕ) (a : Fin 4) (p : PN K n) (m : Fin 4×Fin n →₀ ℕ) :
    coeff m (eulerFamily n a p)=((∑ i : Fin n,m (a,i):ℕ):K)*coeff m p := by
  induction p using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [eulerFamily_monomial]
    simp only [coeff_smul]
    by_cases hm : m=k
    · subst k; simp [coeff_monomial,nsmul_eq_mul]
    · simp [coeff_monomial,hm,Ne.symm hm]
  | add p q hp hq => simp [eulerFamily_add,hp,hq,mul_add]

theorem familySpace_iff_euler [CharZero K] (n : ℕ) (r : Fin 4 → ℕ) (p : PN K n) :
    p∈familySpace n r ↔ ∀ a,eulerFamily n a p=(r a:K) • p := by
  constructor
  · intro hp a
    apply MvPolynomial.ext
    intro m
    rw [coeff_eulerFamily,coeff_smul,smul_eq_mul]
    by_cases hm : m∈p.support
    · rw [hp hm a]
    · simp [MvPolynomial.notMem_support_iff.mp hm]
  · intro hp m hm a
    have he := congrArg (coeff m) (hp a)
    rw [coeff_eulerFamily,coeff_smul,smul_eq_mul] at he
    have hc : coeff m p≠0 := MvPolynomial.mem_support_iff.mp hm
    exact Nat.cast_injective (mul_right_cancel₀ hc he)

def eulerContraction (a : Fin 4) (f : P4 K) : P4 K := ![
  X 0*pderiv 0 f+X 1*pderiv 1 f,
  X 2*pderiv 2 f+X 3*pderiv 3 f,
  X 0*pderiv 0 f+X 2*pderiv 2 f,
  X 1*pderiv 1 f+X 3*pderiv 3 f] a

theorem dw_pullN (n : ℕ) (i : Fin n) (f : P4 K) :
    pderiv (3,i) (pullN n f)=X (0,i)*pullN n (pderiv 1 f)+
      X (1,i)*pullN n (pderiv 3 f) := by
  rw [pd_pullN]
  simp [Fin.sum_univ_succ,coordsN,pd_dotN]

@[simp] theorem pullN_X (n : ℕ) (i : Fin 4) :
    pullN (R:=K) n (X i)=coordsN n i := by simp [pullN]

/-- Euler operators make multidegree reflection independent of the rank. -/
theorem eulerFamily_pullN (n : ℕ) (a : Fin 4) (f : P4 K) :
    eulerFamily n a (pullN n f)=pullN n (eulerContraction a f) := by
  fin_cases a <;>
    simp [eulerFamily,dx_pullN,dz_pullN,dy_pullN,dw_pullN,pullN_X,coordsN,eulerContraction,Finset.sum_add_distrib,
      Finset.sum_mul,Finset.mul_sum,dotN,mul_add,mul_comm,mul_left_comm,mul_assoc]

theorem contraction_degree_reflection [CharZero K] (h : ℕ) (r : Fin 4 → ℕ) (f : P4 K) :
    pullN (2+h) f∈familySpace (2+h) r ↔
      ∀ a,eulerContraction a f=(r a:K) • f := by
  rw [familySpace_iff_euler]
  constructor
  · intro hp a
    apply pullN_injective h
    simpa only [eulerFamily_pullN,map_smul] using hp a
  · intro hp a
    rw [eulerFamily_pullN,hp a,map_smul]

end AMSPhysical

#print axioms AMSPhysical.contraction_degree_reflection
