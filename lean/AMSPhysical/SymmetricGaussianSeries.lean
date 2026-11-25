import GaussianFactorial

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

def symmetricGaussianSeries (q : ℝ) (a : ℕ) : PowerSeries ℝ :=
  PowerSeries.rescale (q^(-(a:ℤ))) (gaussianSeries (q^2) a)

theorem symmetricGaussianSeries_coeff (q : ℝ) (hq : 0<q) (a r : ℕ) :
    PowerSeries.coeff r (symmetricGaussianSeries q a)=
      qfactorial q (a+r)/(qfactorial q a*qfactorial q r) := by
  rw [symmetricGaussianSeries,PowerSeries.coeff_rescale]
  change (q^(-(a:ℤ)))^r*gaussianCoefficient (q^2) a r=_
  rw [gaussianCoefficient_factorial q hq]
  unfold gaussianFactorial
  have hp : (q^(-(a:ℤ)))^r*q^((a*r:ℕ):ℤ)=1 := by
    rw [← zpow_natCast (q^(-(a:ℤ))) r,← zpow_mul,← zpow_add₀ (ne_of_gt hq)]
    have hz : -(a:ℤ)*(r:ℤ)+((a*r:ℕ):ℤ)=0 := by push_cast;ring
    rw [hz,zpow_zero]
  linear_combination (qfactorial q (a+r)/(qfactorial q a*qfactorial q r))*hp

end AMSPhysical
#print axioms AMSPhysical.symmetricGaussianSeries_coeff
