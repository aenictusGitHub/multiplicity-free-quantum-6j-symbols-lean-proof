import QuantumMixedMetric
import QuantumMixedNormTerm
import QuantumMixedNormSum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3600000
noncomputable section
namespace AMSPhysical

/-- Closed mixed symmetric/opposite highest-vector normalization. -/
def mixedCouplingNormClosed (q : ℝ) (n a b r : ℕ) : ℝ :=
  q^(-2*(b:ℤ)*(r:ℤ))*qfactorial q r*qfactorial q a*qfactorial q b*qfactorial q (a+n+b+r)/
    (qfactorial q (r+a)*qfactorial q (r+b)*qfactorial q (a+n+b))

/-- The squared norm of the actual constructed mixed highest vector has a
closed quantum-factorial evaluation, with the rank shift fully proved. -/
theorem mixedHighestVector_norm_closed (q : ℝ) (hq : 0<q) (n a b r : ℕ) (hn : 0<n) :
    mixedTensorBilin q n (r+a) (r+b) (mixedHighestVector q n r a b) (mixedHighestVector q n r a b)=
      mixedCouplingNormClosed q n a b r := by
  rw [mixedHighestVector_norm_sum]
  have he : (∑ t : occupationWeights (Fin (n+1)) r,
      (mixedHighestCoefficient q n r b t)^2*
      occupationCompactWeight q n (r+a) (shiftedOccupation n r a 0 t)*
      occupationOppositeWeight q n (r+b) (shiftedOccupation n r b (Fin.last n) t))=
      mixedNormConstant q n a b r*(∑ t : occupationWeights (Fin (n+1)) r,mixedNormSummand q n a b r t) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    exact mixedHighest_norm_term q hq n r a b t
  rw [he,mixedNormSummand_sum q hq n a b r hn]
  unfold mixedNormConstant mixedCouplingNormClosed
  have hp : q^(-((a:ℤ)+b)*(r:ℤ)+(n:ℤ)*r)*q^(((a:ℤ)-n-b)*(r:ℤ))=q^(-2*(b:ℤ)*(r:ℤ)) := by
    rw [← zpow_add₀ (ne_of_gt hq)]
    congr 1
    ring
  field_simp [qfactorial_ne_zero q hq r,qfactorial_ne_zero q hq (r+a),
    qfactorial_ne_zero q hq (r+b),qfactorial_ne_zero q hq (a+n+b)]
  linear_combination (qfactorial q a*qfactorial q b*qfactorial q (a+n+b+r))*hp

end AMSPhysical
#print axioms AMSPhysical.mixedHighestVector_norm_closed
