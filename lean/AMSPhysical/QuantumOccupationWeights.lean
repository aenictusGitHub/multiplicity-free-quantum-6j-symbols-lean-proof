import QuantumOccupationFactorials

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

def occupationCompactWeight (q : ℝ) (n L : ℕ) (x : occupationWeights (Fin (n+1)) L) : ℝ :=
  q^(occupationEnergy n L x+occupationHeightZ n L x)*occupationFactorialProduct q n L x/qfactorial q L

def occupationDualWeight (q : ℝ) (n L : ℕ) (x : occupationWeights (Fin (n+1)) L) : ℝ :=
  (-1:ℝ)^(occupationHeightZ n L x)*q^(occupationEnergy n L x-occupationHeightZ n L x)*
    occupationFactorialProduct q n L x/qfactorial q L

theorem occupationCompactWeight_pos (q : ℝ) (hq : 0<q) (n L : ℕ)
    (x : occupationWeights (Fin (n+1)) L) : 0<occupationCompactWeight q n L x := by
  exact div_pos (mul_pos (zpow_pos hq _) (occupationFactorialProduct_pos q hq n L x))
    (qfactorial_pos q hq L)

theorem occupationDualWeight_ne_zero (q : ℝ) (hq : 0<q) (n L : ℕ)
    (x : occupationWeights (Fin (n+1)) L) : occupationDualWeight q n L x≠0 := by
  unfold occupationDualWeight
  apply div_ne_zero
  · exact mul_ne_zero (mul_ne_zero (zpow_ne_zero _ (by norm_num)) (zpow_ne_zero _ (ne_of_gt hq)))
      (ne_of_gt (occupationFactorialProduct_pos q hq n L x))
  · exact qfactorial_ne_zero q hq L

theorem occupationFactorialProduct_raised_integer (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ)
    (x : occupationWeights (Fin (n+1)) L) (i : Fin n) (hi : 0<x.val i.succ) :
    qInteger q (x.val i.succ)*occupationFactorialProduct q n L (raisedOccupation n L x i hi)=
      qInteger q (x.val i.castSucc+1)*occupationFactorialProduct q n L x := by
  have he := occupationFactorialProduct_raised q n L x i hi
  rw [qnum_eq_qInteger q hq hq1,qnum_eq_qInteger q hq hq1] at he
  have ha := Int.toNat_of_nonneg (x.property.1 i.castSucc)
  have hb := Int.toNat_of_nonneg (x.property.1 i.succ)
  simpa only [Nat.cast_add,Nat.cast_one,ha,hb] using he

theorem occupationCompactWeight_raised (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ)
    (x : occupationWeights (Fin (n+1)) L) (i : Fin n) (hi : 0<x.val i.succ) :
    qInteger q (x.val i.succ)*occupationCompactWeight q n L (raisedOccupation n L x i hi)=
      q^(simpleOccupationWeight n x.val i)*qInteger q (x.val i.castSucc+1)*occupationCompactWeight q n L x := by
  have he := occupationFactorialProduct_raised_integer q hq hq1 n L x i hi
  have hpow : occupationEnergy n L (raisedOccupation n L x i hi)+occupationHeightZ n L (raisedOccupation n L x i hi)=
      simpleOccupationWeight n x.val i+(occupationEnergy n L x+occupationHeightZ n L x) := by
    rw [raisedOccupation_energy,raisedOccupation_heightZ]
    unfold simpleOccupationWeight
    ring
  unfold occupationCompactWeight
  rw [hpow,zpow_add₀ (ne_of_gt hq)]
  linear_combination (q^(simpleOccupationWeight n x.val i)*
    q^(occupationEnergy n L x+occupationHeightZ n L x)/qfactorial q L)*he

theorem occupationDualWeight_raised (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ)
    (x : occupationWeights (Fin (n+1)) L) (i : Fin n) (hi : 0<x.val i.succ) :
    qInteger q (x.val i.succ)*occupationDualWeight q n L (raisedOccupation n L x i hi)=
      -q^(simpleOccupationWeight n x.val i+2)*qInteger q (x.val i.castSucc+1)*occupationDualWeight q n L x := by
  have he := occupationFactorialProduct_raised_integer q hq hq1 n L x i hi
  have hpow : occupationEnergy n L (raisedOccupation n L x i hi)-occupationHeightZ n L (raisedOccupation n L x i hi)=
      (simpleOccupationWeight n x.val i+2)+(occupationEnergy n L x-occupationHeightZ n L x) := by
    rw [raisedOccupation_energy,raisedOccupation_heightZ]
    unfold simpleOccupationWeight
    ring
  have hsign : (-1:ℝ)^(occupationHeightZ n L (raisedOccupation n L x i hi))= -(-1:ℝ)^(occupationHeightZ n L x) := by
    rw [raisedOccupation_heightZ,zpow_sub₀ (by norm_num : (-1:ℝ)≠0),zpow_one]
    ring
  unfold occupationDualWeight
  rw [hpow,hsign,zpow_add₀ (ne_of_gt hq)]
  linear_combination (-q^(simpleOccupationWeight n x.val i+2)*(-1:ℝ)^(occupationHeightZ n L x)*
    q^(occupationEnergy n L x-occupationHeightZ n L x)/qfactorial q L)*he

end AMSPhysical
#print axioms AMSPhysical.occupationDualWeight_raised
