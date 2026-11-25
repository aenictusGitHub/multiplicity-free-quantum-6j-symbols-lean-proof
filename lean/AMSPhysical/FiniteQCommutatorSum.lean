import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Data.Real.Basic

set_option autoImplicit false
namespace AMSPhysical
theorem finiteQCommutatorSum {A I : Type*} [Ring A] [Module ℝ A] [Fintype I]
    (a : A) (b : I → A) (Q : ℝ) :
    a*(∑ i,b i)-Q • ((∑ i,b i)*a)=∑ i,(a*b i-Q • (b i*a)) := by
  simp only [Finset.mul_sum,Finset.sum_mul,Finset.sum_sub_distrib,Finset.smul_sum]
end AMSPhysical
