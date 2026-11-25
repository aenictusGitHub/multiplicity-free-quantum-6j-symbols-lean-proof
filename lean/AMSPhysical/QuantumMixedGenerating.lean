import QuantumGaussianBlocks
import GaussianFactorial

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

def mixedNormGeneratingSeries (q : ℝ) (a b n : ℕ) : PowerSeries ℝ :=
  gaussianSeries (q^2) a*
    geometricBlock (q^2) (-((n-1:ℕ):ℤ)) (n-1)*
    PowerSeries.rescale ((q^2)^(-((n+b:ℕ):ℤ))) (gaussianSeries (q^2) b)

theorem mixedNormGeneratingSeries_closed (q : ℝ) (hq : q≠0) (a b n : ℕ) (hn : 0<n) :
    mixedNormGeneratingSeries q a b n=
      PowerSeries.rescale ((q^2)^(-((n+b:ℕ):ℤ))) (gaussianSeries (q^2) (a+n+b)) := by
  unfold mixedNormGeneratingSeries
  rw [← geometricBlock_negative]
  exact gaussian_mixed_alphabet (q^2) (pow_ne_zero 2 hq) a b n hn

/-- Closed coefficient evaluation for the merged arbitrary-rank mixed norm
alphabet, with every contraction index and both endpoint degrees free. -/
theorem mixedNormGeneratingSeries_coeff (q : ℝ) (hq : 0<q) (a b n r : ℕ) (hn : 0<n) :
    PowerSeries.coeff r (mixedNormGeneratingSeries q a b n)=
      q^(((a:ℤ)-n-b)*(r:ℤ))*qfactorial q (a+n+b+r)/
        (qfactorial q (a+n+b)*qfactorial q r) := by
  rw [mixedNormGeneratingSeries_closed q (ne_of_gt hq) a b n hn,PowerSeries.coeff_rescale]
  change (((q^2)^(-((n+b:ℕ):ℤ)))^r)*gaussianCoefficient (q^2) (a+n+b) r=_
  rw [gaussianCoefficient_factorial q hq]
  unfold gaussianFactorial
  have hp : (((q^2)^(-((n+b:ℕ):ℤ)))^r)*q^(((a+n+b)*r:ℕ):ℤ)=
      q^(((a:ℤ)-n-b)*(r:ℤ)) := by
    rw [← zpow_natCast ((q^2)^(-((n+b:ℕ):ℤ))) r,← zpow_mul,
      ← zpow_natCast q 2,← zpow_mul,← zpow_add₀ (ne_of_gt hq)]
    congr 1
    push_cast
    ring
  linear_combination (qfactorial q (a+n+b+r)/(qfactorial q (a+n+b)*qfactorial q r))*hp

end AMSPhysical
#print axioms AMSPhysical.mixedNormGeneratingSeries_coeff
