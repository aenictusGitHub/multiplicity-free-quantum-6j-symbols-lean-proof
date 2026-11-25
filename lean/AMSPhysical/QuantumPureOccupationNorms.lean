import QuantumOccupationShiftNorm
import QuantumOppositeWeight
import QuantumTypeADualSymmetric

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem pureOccupation_energy (n L : ℕ) (k : Fin (n+1))
    (x : occupationWeights (Fin (n+1)) L) (hx : x.val=Pi.single k (L:ℤ)) :
    occupationEnergy n L x=0 := by
  unfold occupationEnergy occupationSquareSum
  rw [hx]
  simp [Pi.single_apply,eq_comm]

theorem pureOccupation_height (n L : ℕ) (k : Fin (n+1))
    (x : occupationWeights (Fin (n+1)) L) (hx : x.val=Pi.single k (L:ℤ)) :
    occupationHeightZ n L x=(k.val:ℤ)*L := by
  unfold occupationHeightZ latticePairing
  rw [hx]
  simp [Pi.single_apply,eq_comm,mul_ite]

theorem pureOccupation_factorials (q : ℝ) (n L : ℕ) (k : Fin (n+1))
    (x : occupationWeights (Fin (n+1)) L) (hx : x.val=Pi.single k (L:ℤ)) :
    occupationFactorialProduct q n L x=qfactorial q L := by
  unfold occupationFactorialProduct
  rw [hx]
  simp [Pi.single_apply,qfactorial_zero,apply_ite]

theorem occupationCompactWeight_highest (q : ℝ) (hq : 0<q) (n L : ℕ) :
    occupationCompactWeight q n L (highestOccupation n L)=1 := by
  unfold occupationCompactWeight
  rw [pureOccupation_energy n L 0 _ rfl,pureOccupation_height n L 0 _ rfl,
    pureOccupation_factorials q n L 0 _ rfl]
  simp [qfactorial_ne_zero q hq L]

theorem occupationOppositeWeight_highest (q : ℝ) (hq : 0<q) (n L : ℕ) :
    occupationOppositeWeight q n L (lowestOccupation n L)=1 := by
  unfold occupationOppositeWeight
  rw [pureOccupation_energy n L (Fin.last n) _ rfl,pureOccupation_height n L (Fin.last n) _ rfl,
    pureOccupation_factorials q n L (Fin.last n) _ rfl]
  simp only [Fin.val_last,zero_sub,Nat.cast_mul]
  rw [← zpow_add₀ (ne_of_gt hq),add_neg_cancel,zpow_zero,one_mul]
  exact div_self (qfactorial_ne_zero q hq L)

end AMSPhysical
#print axioms AMSPhysical.occupationOppositeWeight_highest
