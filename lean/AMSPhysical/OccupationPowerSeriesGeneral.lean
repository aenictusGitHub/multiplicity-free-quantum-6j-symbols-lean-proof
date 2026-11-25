import OccupationPowerSeries

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem occupation_powerSeries_coefficient (P : ι → PowerSeries ℝ) (r : ℕ) :
    (∑ x : occupationWeights ι r,∏ i,PowerSeries.coeff ((x.val i).toNat) (P i))=
      PowerSeries.coeff r (∏ i,P i) := by
  classical
  rw [PowerSeries.coeff_prod]
  apply Finset.sum_bij (fun x _ => occupationNatFunction r x)
  · intro x hx
    apply Finset.mem_finsuppAntidiag.mpr
    exact ⟨occupationNatFunction_sum r x,Finset.subset_univ _⟩
  · intro x hx y hy he
    exact occupationNatFunction_injective r he
  · intro f hf
    have hh := (Finset.mem_finsuppAntidiag.mp hf).1
    exact ⟨occupationOfNatSum r f hh,Finset.mem_univ _,occupationNatFunction_ofNatSum r f hh⟩
  · intro x hx
    apply Finset.prod_congr rfl
    intro i hi
    rw [occupationNatFunction_apply]

end AMSPhysical
#print axioms AMSPhysical.occupation_powerSeries_coefficient
