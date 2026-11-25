import QuantumOccupationWeights

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

/-- Positive compact weight for the Chevalley-twisted opposite module,
normalized at its actual highest vector at the last vertex. -/
def occupationOppositeWeight (q : ℝ) (n L : ℕ) (x : occupationWeights (Fin (n+1)) L) : ℝ :=
  q^((n*L:ℕ):ℤ)*q^(occupationEnergy n L x-occupationHeightZ n L x)*
    occupationFactorialProduct q n L x/qfactorial q L

theorem occupationOppositeWeight_pos (q : ℝ) (hq : 0<q) (n L : ℕ)
    (x : occupationWeights (Fin (n+1)) L) : 0<occupationOppositeWeight q n L x := by
  exact div_pos (mul_pos (mul_pos (zpow_pos hq _) (zpow_pos hq _))
    (occupationFactorialProduct_pos q hq n L x)) (qfactorial_pos q hq L)

theorem occupationOppositeWeight_raised (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n L : ℕ)
    (x : occupationWeights (Fin (n+1)) L) (i : Fin n) (hi : 0<x.val i.succ) :
    qInteger q (x.val i.succ)*occupationOppositeWeight q n L (raisedOccupation n L x i hi)=
      q^(simpleOccupationWeight n x.val i+2)*qInteger q (x.val i.castSucc+1)*occupationOppositeWeight q n L x := by
  have he := occupationFactorialProduct_raised_integer q hq hq1 n L x i hi
  have hpow : occupationEnergy n L (raisedOccupation n L x i hi)-occupationHeightZ n L (raisedOccupation n L x i hi)=
      (simpleOccupationWeight n x.val i+2)+(occupationEnergy n L x-occupationHeightZ n L x) := by
    rw [raisedOccupation_energy,raisedOccupation_heightZ]
    unfold simpleOccupationWeight
    ring
  unfold occupationOppositeWeight
  rw [hpow,zpow_add₀ (ne_of_gt hq)]
  linear_combination (q^((n*L:ℕ):ℤ)*q^(simpleOccupationWeight n x.val i+2)*
    q^(occupationEnergy n L x-occupationHeightZ n L x)/qfactorial q L)*he

end AMSPhysical
#print axioms AMSPhysical.occupationOppositeWeight_raised
