import Determinant
import Mathlib.Algebra.BigOperators.Finsupp.Basic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace AMSPhysical
open MvPolynomial

variable {K σ : Type*} [Field K] [Fintype σ] [DecidableEq σ]

def exponentWeight (w : σ → ℤ) (m : σ →₀ ℕ) : ℤ := ∑ i, (m i:ℤ)*w i

def HasPolynomialWeight (w : σ → ℤ) (r : ℤ) (p : MvPolynomial σ K) : Prop :=
  ∀ m∈p.support, exponentWeight w m=r

def weightScale (w : σ → ℤ) (t : K) (v : σ → K) : σ → K :=
  fun i => t^(w i)*v i

theorem zpow_fintype_sum (t : K) (ht : t≠0) (f : σ → ℤ) :
    t^(∑ i,f i)=∏ i,t^(f i) := by
  have he (s : Finset σ) : t^(∑ i∈s,f i)=∏ i∈s,t^(f i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi hs => simp [hi,zpow_add₀ ht,hs]
  exact he Finset.univ

theorem eval_weightScale_monomial (w : σ → ℤ) (t : K) (ht : t≠0)
    (v : σ → K) (m : σ →₀ ℕ) (a : K) :
    eval (weightScale w t v) (monomial m a)=
      t^(exponentWeight w m)*eval v (monomial m a) := by
  simp only [eval_monomial,weightScale,mul_pow]
  rw [Finsupp.prod_fintype _ _ (by simp),Finsupp.prod_fintype _ _ (by simp)]
  rw [Finset.prod_mul_distrib]
  have he : (∏ i,(t^(w i))^(m i))=t^(exponentWeight w m) := by
    rw [exponentWeight,zpow_fintype_sum t ht]
    apply Finset.prod_congr rfl
    intro i hi
    rw [mul_comm (m i:ℤ),zpow_mul,zpow_natCast]
  rw [he]
  ring

theorem eval_weightScale (w : σ → ℤ) (r : ℤ) (p : MvPolynomial σ K)
    (hp : HasPolynomialWeight w r p) (t : K) (ht : t≠0) (v : σ → K) :
    eval (weightScale w t v) p=t^r*eval v p := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [eval_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [eval_weightScale_monomial w t ht, hp m hm]

end AMSPhysical

#print axioms AMSPhysical.eval_weightScale
