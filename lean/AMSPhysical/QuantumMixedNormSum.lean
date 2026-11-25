import QuantumMixedNormSlotProduct
import QuantumMixedNormSummand

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem mixedNormSummand_sum (q : ℝ) (hq : 0<q) (n a b r : ℕ) (hn : 0<n) :
    (∑ t : occupationWeights (Fin (n+1)) r,mixedNormSummand q n a b r t)=
      (qfactorial q a*qfactorial q b)*q^(((a:ℤ)-n-b)*(r:ℤ))*qfactorial q (a+n+b+r)/
        (qfactorial q (a+n+b)*qfactorial q r) := by
  have he : (∑ t : occupationWeights (Fin (n+1)) r,mixedNormSummand q n a b r t)=
      PowerSeries.coeff r (∏ k : Fin (n+1),mixedNormSlot q a b n k) := by
    rw [← occupation_powerSeries_coefficient]
    apply Finset.sum_congr rfl
    intro t ht
    exact (mixedNormSlot_coeff_product q hq n a b r hn t).symm
  rw [he,mixedNormSlot_product q a b n hn,PowerSeries.coeff_C_mul,mixedNormGeneratingSeries_coeff q hq a b n r hn]
  ring

end AMSPhysical
#print axioms AMSPhysical.mixedNormSummand_sum
