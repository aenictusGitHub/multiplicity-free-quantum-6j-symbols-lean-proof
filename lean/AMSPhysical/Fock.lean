import Determinant
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Factorial.BigOperators

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace AMSPhysical
open MvPolynomial

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def monomialWeight (m : σ →₀ ℕ) : ℕ := ∏ i, (m i).factorial

theorem monomialWeight_pos (m : σ →₀ ℕ) : 0<monomialWeight m := by
  exact Finset.prod_pos fun i _ => Nat.factorial_pos (m i)

theorem monomialWeight_add_single (m : σ →₀ ℕ) (i : σ) :
    monomialWeight (m+Finsupp.single i 1)=(m i+1)*monomialWeight m := by
  have he : ∀ j : σ, ((m+Finsupp.single i 1 : σ →₀ ℕ) j).factorial =
      (if j=i then m i+1 else 1)*(m j).factorial := by
    intro j
    by_cases hj : j=i
    · subst j
      simp [Nat.factorial_succ]
    · simp [Finsupp.single_eq_of_ne hj,hj]
  unfold monomialWeight
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  simp

/-- The polynomial Fock pairing, with conjugate-linear first argument. -/
def fock (p q : MvPolynomial σ ℂ) : ℂ :=
  p.sum fun m a => star a * coeff m q * (monomialWeight m : ℂ)

theorem fock_add_left (p q r : MvPolynomial σ ℂ) :
    fock (p+q) r=fock p r+fock q r := by
  unfold fock
  apply Finsupp.sum_add_index'
  · intro m
    simp
  · intro m a b
    simp [add_mul]

theorem fock_add_right (p q r : MvPolynomial σ ℂ) :
    fock p (q+r)=fock p q+fock p r := by
  simp [fock,sum_def,mul_add,add_mul,Finset.sum_add_distrib]

@[simp] theorem fock_zero_left (p : MvPolynomial σ ℂ) : fock 0 p=0 := by
  simp [fock]

@[simp] theorem fock_zero_right (p : MvPolynomial σ ℂ) : fock p 0=0 := by
  simp [fock,sum_def]

theorem fock_monomial_left (m : σ →₀ ℕ) (a : ℂ) (q : MvPolynomial σ ℂ) :
    fock (monomial m a) q=star a*coeff m q*(monomialWeight m:ℂ) := by
  simp [fock]

theorem fock_monomials (m n : σ →₀ ℕ) (a b : ℂ) :
    fock (monomial m a) (monomial n b)=
      if m=n then star a*b*(monomialWeight m:ℂ) else 0 := by
  rw [fock_monomial_left]
  by_cases h : m=n <;> simp [h,coeff_monomial,eq_comm]

theorem fock_smul_left (c : ℂ) (p q : MvPolynomial σ ℂ) :
    fock (c • p) q=star c*fock p q := by
  induction p using MvPolynomial.induction_on' with
  | monomial m a =>
    simp only [smul_monomial,fock_monomial_left,smul_eq_mul,star_mul]
    ring
  | add p r hp hr =>
    simp only [smul_add,fock_add_left,hp,hr,mul_add]

theorem fock_conj_symm (p q : MvPolynomial σ ℂ) : star (fock q p)=fock p q := by
  induction p using MvPolynomial.induction_on' with
  | monomial m a =>
    induction q using MvPolynomial.induction_on' with
    | monomial n b =>
      by_cases h : m=n
      · subst n
        simp [fock_monomials,star_mul,mul_comm,mul_left_comm,mul_assoc]
      · simp [fock_monomials,h,Ne.symm h]
    | add q r hq hr => simp only [fock_add_left,fock_add_right,star_add,hq,hr]
  | add p r hp hr => simp only [fock_add_left,fock_add_right,star_add,hp,hr]

theorem fock_smul_right (c : ℂ) (p q : MvPolynomial σ ℂ) :
    fock p (c • q)=c*fock p q := by
  rw [← fock_conj_symm, fock_smul_left,star_mul,star_star,fock_conj_symm]
  ring

theorem fock_mulX_pderiv_monomials (i : σ) (m n : σ →₀ ℕ) (a b : ℂ) :
    fock (X i * monomial m a) (monomial n b)=
      fock (monomial m a) (pderiv i (monomial n b)) := by
  rw [X,monomial_mul,one_mul,pderiv_monomial]
  by_cases he : Finsupp.single i 1+m=n
  · subst n
    have hc : ((Finsupp.single i 1+m : σ →₀ ℕ) i)=m i+1 := by simp; omega
    have hs : (Finsupp.single i 1+m : σ →₀ ℕ)-Finsupp.single i 1=m := by simp
    rw [hs,hc,fock_monomials,fock_monomials,if_pos rfl,if_pos rfl]
    rw [add_comm (Finsupp.single i 1) m,monomialWeight_add_single]
    push_cast
    ring
  · by_cases hn : n i=0
    · simp [fock_monomials,he,hn]
    · have hs : n-Finsupp.single i 1+Finsupp.single i 1=n :=
        Finsupp.sub_add_single_one_cancel hn
      have hm : m≠n-Finsupp.single i 1 := by
        intro hm
        apply he
        rw [hm,add_comm]
        exact hs
      simp [fock_monomials,he,hm]

/-- Creation and annihilation are adjoint for the actual factorial pairing. -/
theorem fock_mulX_pderiv (i : σ) (p q : MvPolynomial σ ℂ) :
    fock (X i*p) q=fock p (pderiv i q) := by
  induction p using MvPolynomial.induction_on' with
  | monomial m a =>
    induction q using MvPolynomial.induction_on' with
    | monomial n b => exact fock_mulX_pderiv_monomials i m n a b
    | add q r hq hr => simp only [map_add,fock_add_right,hq,hr]
  | add p r hp hr => simp only [mul_add,fock_add_left,hp,hr]

theorem fock_pderiv_mulX (i : σ) (p q : MvPolynomial σ ℂ) :
    fock (pderiv i p) q=fock p (X i*q) := by
  rw [← fock_conj_symm, ← fock_mulX_pderiv, fock_conj_symm]

theorem fock_sum_left {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial σ ℂ)
    (q : MvPolynomial σ ℂ) : fock (∑ i∈s,p i) q=∑ i∈s,fock (p i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs => simp [hi,hs,fock_add_left]

theorem fock_sum_right {ι : Type*} (s : Finset ι) (p : MvPolynomial σ ℂ)
    (q : ι → MvPolynomial σ ℂ) : fock p (∑ i∈s,q i)=∑ i∈s,fock p (q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs => simp [hi,hs,fock_add_right]

theorem fock_diag_re (p : MvPolynomial σ ℂ) :
    (fock p p).re=∑ m∈p.support,Complex.normSq (coeff m p)*(monomialWeight m:ℝ) := by
  unfold fock
  rw [sum_def,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Complex.star_def,← Complex.normSq_eq_conj_mul_self]
  simp

theorem fock_nonneg (p : MvPolynomial σ ℂ) : 0≤(fock p p).re := by
  rw [fock_diag_re]
  exact Finset.sum_nonneg fun m _ => mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

theorem fock_definite (p : MvPolynomial σ ℂ) (hp : fock p p=0) : p=0 := by
  have hs : ∑ m∈p.support,Complex.normSq (coeff m p)*(monomialWeight m:ℝ)=0 := by
    rw [← fock_diag_re,hp]
    rfl
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun m (_ : m∈p.support) => mul_nonneg (Complex.normSq_nonneg (coeff m p))
      (Nat.cast_nonneg (monomialWeight m) : (0:ℝ)≤_))).mp hs
  apply MvPolynomial.ext
  intro m
  by_cases hm : m∈p.support
  · have he := hz m hm
    have hw : (monomialWeight m:ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr (monomialWeight_pos m))
    have hnorm : Complex.normSq (coeff m p)=0 := (mul_eq_zero.mp he).resolve_right hw
    simpa using Complex.normSq_eq_zero.mp hnorm
  · simpa using MvPolynomial.notMem_support_iff.mp hm

end AMSPhysical

#print axioms AMSPhysical.monomialWeight_add_single
#print axioms AMSPhysical.fock_monomials
