import QuantumOppositeWeight

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

def occupationDualSign (n L : ℕ) (x : occupationWeights (Fin (n+1)) L) : ℝ :=
  (-1:ℝ)^(occupationHeightZ n L x)

theorem occupationDualSign_square (n L : ℕ) (x : occupationWeights (Fin (n+1)) L) :
    occupationDualSign n L x*occupationDualSign n L x=1 := by
  unfold occupationDualSign
  rw [← mul_zpow]
  norm_num

theorem occupationDualSign_raised (n L : ℕ) (x : occupationWeights (Fin (n+1)) L)
    (i : Fin n) (hi : 0<x.val i.succ) :
    occupationDualSign n L (raisedOccupation n L x i hi)= -occupationDualSign n L x := by
  unfold occupationDualSign
  rw [raisedOccupation_heightZ,zpow_sub₀ (by norm_num : (-1:ℝ)≠0),zpow_one]
  ring

theorem occupationDualWeight_physical (q : ℝ) (n L : ℕ) (x : occupationWeights (Fin (n+1)) L) :
    q^((n*L:ℕ):ℤ)*occupationDualWeight q n L x=
      occupationDualSign n L x*occupationOppositeWeight q n L x := by
  unfold occupationDualWeight occupationDualSign occupationOppositeWeight
  ring

end AMSPhysical
