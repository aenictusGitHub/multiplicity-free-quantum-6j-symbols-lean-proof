import QuantumMixedCoefficientClosed
import QuantumOppositeWeight
import QuantumOccupationShiftNorm
import QuantumMixedNormSummand

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 6000000
noncomputable section
namespace AMSPhysical

def mixedNormConstant (q : ℝ) (n a b r : ℕ) : ℝ :=
  q^(-((a:ℤ)+b)*(r:ℤ)+(n:ℤ)*r)*(qfactorial q r)^2/
    (qfactorial q (r+a)*qfactorial q (r+b))

/-- Exact reduction of each term of the actual tensor norm to the
multivariate geometric-alphabet summand. -/
theorem mixedHighest_norm_term (q : ℝ) (hq : 0<q) (n r a b : ℕ)
    (t : occupationWeights (Fin (n+1)) r) :
    (mixedHighestCoefficient q n r b t)^2*
      occupationCompactWeight q n (r+a) (shiftedOccupation n r a 0 t)*
      occupationOppositeWeight q n (r+b) (shiftedOccupation n r b (Fin.last n) t)=
      mixedNormConstant q n a b r*mixedNormSummand q n a b r t := by
  have hs : ((-1:ℝ)^(occupationHeightZ n r t))^2=1 := by
    have hn : ((occupationHeight n r t):ℤ)=occupationHeightZ n r t :=
      Int.toNat_of_nonneg (occupationHeightZ_nonnegative n r t)
    rw [← hn,zpow_natCast,← pow_mul,mul_comm _ 2,pow_mul]
    norm_num
  have h0 := shiftedOccupation_factorials q n r a 0 t
  have hN := shiftedOccupation_factorials q n r b (Fin.last n) t
  have h0' : occupationFactorialProduct q n (r+a) (shiftedOccupation n r a 0 t)=
      qfactorial q (a+(t.val 0).toNat)*occupationFactorialProduct q n r t/qfactorial q ((t.val 0).toNat) := by
    apply (eq_div_iff (qfactorial_ne_zero q hq _)).mpr
    rw [mul_comm]
    simpa only [Nat.add_comm] using h0
  have hN' : occupationFactorialProduct q n (r+b) (shiftedOccupation n r b (Fin.last n) t)=
      qfactorial q (b+(t.val (Fin.last n)).toNat)*occupationFactorialProduct q n r t/
        qfactorial q ((t.val (Fin.last n)).toNat) := by
    apply (eq_div_iff (qfactorial_ne_zero q hq _)).mpr
    rw [mul_comm]
    simpa only [Nat.add_comm] using hN
  have hp : (q^(-occupationEnergy n r t-occupationHeightZ n r t-(b:ℤ)*t.val (Fin.last n)))^2*
      q^(occupationEnergy n (r+a) (shiftedOccupation n r a 0 t)+
        occupationHeightZ n (r+a) (shiftedOccupation n r a 0 t))*
      q^((n*(r+b):ℕ):ℤ)*
      q^(occupationEnergy n (r+b) (shiftedOccupation n r b (Fin.last n) t)-
        occupationHeightZ n (r+b) (shiftedOccupation n r b (Fin.last n) t))=
      q^(-((a:ℤ)+b)*(r:ℤ)+(n:ℤ)*r)*
        q^((a:ℤ)*t.val 0-(b:ℤ)*t.val (Fin.last n)-2*occupationHeightZ n r t) := by
    rw [sq,← zpow_add₀ (ne_of_gt hq),← zpow_add₀ (ne_of_gt hq),
      ← zpow_add₀ (ne_of_gt hq),← zpow_add₀ (ne_of_gt hq),← zpow_add₀ (ne_of_gt hq)]
    congr 1
    rw [shiftedOccupation_energy,shiftedOccupation_energy,shiftedOccupation_heightZ,shiftedOccupation_heightZ]
    simp only [Fin.val_zero,Fin.val_last,Nat.cast_add,Nat.cast_mul,Nat.cast_zero,zero_mul,add_zero]
    ring
  rw [mixedHighestCoefficient_factorial q hq]
  unfold occupationCompactWeight occupationOppositeWeight
  rw [h0',hN',div_pow,mul_pow,mul_pow,hs,one_mul]
  unfold mixedNormConstant mixedNormSummand
  have hF := ne_of_gt (occupationFactorialProduct_pos q hq n r t)
  field_simp [hF,qfactorial_ne_zero q hq r,qfactorial_ne_zero q hq (r+a),
    qfactorial_ne_zero q hq (r+b),qfactorial_ne_zero q hq ((t.val 0).toNat),
    qfactorial_ne_zero q hq ((t.val (Fin.last n)).toNat)]
  linear_combination (qfactorial q (a+(t.val 0).toNat)*
    qfactorial q (b+(t.val (Fin.last n)).toNat))*hp

end AMSPhysical
#print axioms AMSPhysical.mixedHighest_norm_term
