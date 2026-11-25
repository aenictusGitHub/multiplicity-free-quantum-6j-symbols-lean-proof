import QShiftedFactorial
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

theorem qPochhammer_add (Q a : ℝ) (m n : ℕ) :
    qPochhammer Q a (m+n)=qPochhammer Q a m*qPochhammer Q (a*Q^m) n := by
  unfold qPochhammer
  rw [Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [pow_add]
  ring

theorem prod_base_powers (Q : ℝ) (n : ℕ) :
    (∏ j ∈ Finset.range n,Q^j)=Q^(n.choose 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ,ih,← pow_add,Nat.choose_succ_succ,Nat.choose_one_right]
    congr 1
    change n.choose 2+n=n+n.choose 2
    omega

/-- Exact finite product reflection; the nonzero base and parameter are the
only restrictions. -/
theorem qPochhammer_reflection (Q a : ℝ) (hQ : Q≠0) (ha : a≠0) (n : ℕ) :
    qPochhammer Q a n=(-a)^n*Q^(n.choose 2)*qPochhammer Q (Q^(1-(n:ℤ))/a) n := by
  unfold qPochhammer
  rw [← Finset.prod_range_reflect (fun j => 1-a*Q^j) n]
  have he (j : ℕ) (hj : j∈Finset.range n) :
      1-a*Q^(n-1-j)=((-a)*Q^(n-1-j))*(1-(Q^(1-(n:ℤ))/a)*Q^j) := by
    have hjn := Finset.mem_range.mp hj
    have hp : Q^(n-1-j)*Q^(1-(n:ℤ))*Q^j=1 := by
      rw [← zpow_natCast Q (n-1-j),← zpow_natCast Q j,← zpow_add₀ hQ,← zpow_add₀ hQ]
      have hz : ((n-1-j:ℕ):ℤ)+(1-(n:ℤ))+(j:ℤ)=0 := by omega
      rw [hz,zpow_zero]
    have hc : (a*Q^(n-1-j))*((Q^(1-(n:ℤ))/a)*Q^j)=1 := by
      calc
        _ = Q^(n-1-j)*Q^(1-(n:ℤ))*Q^j := by field_simp [ha]
        _ = 1 := hp
    linear_combination -hc
  calc
    _ = ∏ j ∈ Finset.range n,((-a)*Q^(n-1-j))*(1-(Q^(1-(n:ℤ))/a)*Q^j) := by
      apply Finset.prod_congr rfl
      exact he
    _ = _ := by
      rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_range,
        Finset.prod_range_reflect,prod_base_powers,mul_assoc]

/-- A split product with its final interval reflected. This form retains
cancellation information when a later quotient has a removable zero. -/
theorem qPochhammer_reflected_suffix (Q a : ℝ) (hQ : Q≠0) (ha : a≠0)
    (k j : ℕ) (hj : j≤k) :
    qPochhammer Q a k=qPochhammer Q a (k-j)*
      ((-(a*Q^(k-j)))^j*Q^(j.choose 2)*qPochhammer Q (Q^(1-(k:ℤ))/a) j) := by
  have hk : k=(k-j)+j := by omega
  conv_lhs => rw [hk,qPochhammer_add]
  rw [qPochhammer_reflection Q (a*Q^(k-j)) hQ (mul_ne_zero ha (pow_ne_zero _ hQ)) j]
  congr 3
  have he : Q^(1-(j:ℤ))/(a*Q^(k-j))=Q^(1-(k:ℤ))/a := by
    rw [← zpow_natCast Q (k-j)]
    have hz : 1-(j:ℤ)=(1-(k:ℤ))+((k-j:ℕ):ℤ) := by omega
    rw [hz,zpow_add₀ hQ]
    field_simp [ha,zpow_ne_zero ((k-j:ℕ):ℤ) hQ]
  rw [he]

end AMSPhysical

#print axioms AMSPhysical.qPochhammer_reflection
#print axioms AMSPhysical.qPochhammer_reflected_suffix
