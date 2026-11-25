import ComplexQuantumFactorials
import QuantumClebschFirstZero

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical

def complexCouplingNormClosed (q:ℂ) (a b r:ℕ):ℂ:=
  q^(-2*(r:ℤ)*(b:ℤ))*complexQfactorial q r*complexQfactorial q a*complexQfactorial q b*
    complexQfactorial q (a+b+r+1)/
    (complexQfactorial q (a+r)*complexQfactorial q (b+r)*complexQfactorial q (a+b+1))

theorem complexCouplingNormClosed_ofReal (q:ℝ) (a b r:ℕ):
    complexCouplingNormClosed (q:ℂ) a b r=(couplingNormClosed q a b r:ℂ):=by
  simp only [complexCouplingNormClosed,couplingNormClosed,complexQfactorial_ofReal,
    Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_zpow]

def complexClebschFactorialTerm (q:ℂ) (l m r a u k:ℕ):ℂ:=
  (-1:ℂ)^k*q^((k:ℤ)*((a:ℤ)-(coupledLabel l m r:ℤ)-1))*complexQfactorial q (l-k)*complexQfactorial q (m-r+k)/
    (complexQfactorial q k*complexQfactorial q (r-k)*complexQfactorial q (descendantIndex a k u)*
      complexQfactorial q (a-descendantIndex a k u))

def complexClebschFactorialSum (q:ℂ) (l m r a u:ℕ):ℂ:=
  ∑ k∈Finset.range (r+1),if DescendantAdmissible a k u then complexClebschFactorialTerm q l m r a u k else 0

def complexRegularClebschCoefficient (q:ℂ) (l m r a u v:ℕ):ℂ:=
  (complexPositiveRoot (complexCouplingNormClosed q (l-r) (m-r) r))⁻¹*
    q^(((a:ℤ)-(u:ℤ))*((u:ℤ)-(l:ℤ)))*complexQfactorial q r*complexQfactorial q a*
    complexQfactorial q (coupledLabel l m r-a)/
    (complexQfactorial q (coupledLabel l m r)*complexQfactorial q (l-u)*complexQfactorial q (m-v))*
      complexClebschFactorialSum q l m r a u

/-- Independent finite Clebsch--Gordan coefficients, with exact weight
support. These are not recoupling coefficients or an AMS expression. -/
def complexClebschCoefficient (q:ℂ) (l m r a u v:ℕ):ℂ:=
  if u+v=r+a then complexRegularClebschCoefficient q l m r a u v else 0

theorem complexClebschFactorialTerm_ofReal (q:ℝ) (l m r a u k:ℕ):
    complexClebschFactorialTerm (q:ℂ) l m r a u k=(clebschFactorialTerm q l m r a u k:ℂ):=by
  simp only [complexClebschFactorialTerm,clebschFactorialTerm,complexQfactorial_ofReal,
    Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_zpow,Complex.ofReal_pow,
    Complex.ofReal_neg,Complex.ofReal_one]

theorem complexClebschFactorialSum_ofReal (q:ℝ) (l m r a u:ℕ):
    complexClebschFactorialSum (q:ℂ) l m r a u=(clebschFactorialSum q l m r a u:ℂ):=by
  simp only [complexClebschFactorialSum,clebschFactorialSum,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs
  · exact complexClebschFactorialTerm_ofReal q l m r a u k
  · rfl

theorem complexRegularClebschCoefficient_ofReal (q:ℝ) (hq:0<q) (l m r a u v:ℕ):
    complexRegularClebschCoefficient (q:ℂ) l m r a u v=(regularClebschFactorialCoefficient q l m r a u v:ℂ):=by
  simp only [complexRegularClebschCoefficient,regularClebschFactorialCoefficient,
    complexCouplingNormClosed_ofReal,complexPositiveRoot_ofReal _ (couplingNormClosed_pos q hq _ _ _),
    complexQfactorial_ofReal,complexClebschFactorialSum_ofReal,
    Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_zpow,Complex.ofReal_inv]

/-- Exact agreement with the actual independently constructed isometric CG
map on the positive-real physical domain. -/
theorem complexClebschCoefficient_ofReal_actual (q:ℝ) (hq:0<q) (hq1:q≠1) (l m:ℕ)
    (r:Fin (min l m+1)) (a:Fin (coupledLabel l m r+1)) (u:Fin (l+1)) (v:Fin (m+1)):
    complexClebschCoefficient (q:ℂ) l m r.val a.val u.val v.val=
      (standardClebschCoefficient q hq hq1 l m r a (u.val:ℤ) (v.val:ℤ):ℂ):=by
  unfold complexClebschCoefficient
  by_cases huv:u.val+v.val=r.val+a.val
  · rw [if_pos huv,standardClebschCoefficient_factorial q hq hq1 l m r a u.val v.val
      (by have h:=u.isLt;omega) (by have h:=v.isLt;omega) huv]
    exact complexRegularClebschCoefficient_ofReal q hq l m r.val a.val u.val v.val
  · rw [if_neg huv,standardClebschCoefficient_weight_mismatch q hq hq1 l m r a u.val v.val
      (by exact_mod_cast huv),Complex.ofReal_zero]

end AMSPhysical
#print axioms AMSPhysical.complexClebschCoefficient_ofReal_actual
