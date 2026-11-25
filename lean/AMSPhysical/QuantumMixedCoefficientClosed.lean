import QuantumMixedCoefficient

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

/-- Closed quantum-factorial form of the actual mixed highest-vector coefficients. -/
theorem mixedHighestCoefficient_factorial (q : ℝ) (hq : 0<q) (n r b : ℕ)
    (t : occupationWeights (Fin (n+1)) r) :
    mixedHighestCoefficient q n r b t=
      (-1:ℝ)^(occupationHeightZ n r t)*
      q^(-occupationEnergy n r t-occupationHeightZ n r t-(b:ℤ)*t.val (Fin.last n))*
      qfactorial q r/occupationFactorialProduct q n r t := by
  unfold mixedHighestCoefficient occupationCompactWeight
  rw [div_div_eq_mul_div]
  have hp : q^(-occupationEnergy n r t-occupationHeightZ n r t-(b:ℤ)*t.val (Fin.last n))*
      q^(occupationEnergy n r t+occupationHeightZ n r t)=q^(-(b:ℤ)*t.val (Fin.last n)) := by
    rw [← zpow_add₀ (ne_of_gt hq)]
    congr 1
    ring
  have hF := ne_of_gt (occupationFactorialProduct_pos q hq n r t)
  have hqE := zpow_ne_zero (occupationEnergy n r t+occupationHeightZ n r t) (ne_of_gt hq)
  field_simp [hF,hqE]
  linear_combination -(qfactorial q r)*hp

end AMSPhysical
#print axioms AMSPhysical.mixedHighestCoefficient_factorial
