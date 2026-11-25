import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false
namespace AMSPhysical
theorem finiteCommutatorSum {A I : Type*} [Ring A] [Fintype I] (a : A) (b : I → A) :
    a*(∑ i,b i)-(∑ i,b i)*a=∑ i,(a*b i-b i*a) := by
  simp only [Finset.mul_sum,Finset.sum_mul,Finset.sum_sub_distrib]
end AMSPhysical
