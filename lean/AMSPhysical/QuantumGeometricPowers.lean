import QuantumPrefixTelescoping

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

theorem qGeometricInteger_nat_succ (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (t : ℕ) :
    qGeometricInteger q ((t+1:ℕ):ℤ)=qGeometricInteger q (t:ℤ)+(q^(-2:ℤ))^t := by
  rw [Nat.cast_add,Nat.cast_one,qGeometricInteger_add q hq]
  have h1 : qGeometricInteger q 1=1 := by simp only [qGeometricInteger,sub_self,zpow_zero,qInteger_one q hD,mul_one]
  rw [h1,mul_one]
  congr 1
  rw [zpow_mul,zpow_natCast]

theorem qGeometricInteger_nat_closed (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0) (t : ℕ) :
    (∑ j∈Finset.range t,(q^(-2:ℤ))^j)=q^(1-(t:ℤ))*qInteger q (t:ℤ) := by
  change (∑ j∈Finset.range t,(q^(-2:ℤ))^j)=qGeometricInteger q (t:ℤ)
  induction t with
  | zero => simp [qGeometricInteger_zero]
  | succ t ih => rw [Finset.sum_range_succ,ih,qGeometricInteger_nat_succ q hq hD]

end AMSPhysical
