import QuantumOccupationShifts
import QuantumOccupationWeights
import QuantumTypeAInverseWeights

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace AMSPhysical

/-- Candidate mixed highest-vector coefficients, expressed through the
independently proved positive compact weights. -/
def mixedHighestCoefficient (q : ℝ) (n r b : ℕ) (t : occupationWeights (Fin (n+1)) r) : ℝ :=
  (-1:ℝ)^(occupationHeightZ n r t)*q^(-(b:ℤ)*t.val (Fin.last n))/occupationCompactWeight q n r t

theorem mixedHighestCoefficient_ne_zero (q : ℝ) (hq : 0<q) (n r b : ℕ)
    (t : occupationWeights (Fin (n+1)) r) : mixedHighestCoefficient q n r b t≠0 := by
  unfold mixedHighestCoefficient
  exact div_ne_zero (mul_ne_zero (zpow_ne_zero _ (by norm_num)) (zpow_ne_zero _ (ne_of_gt hq)))
    (ne_of_gt (occupationCompactWeight_pos q hq n r t))

theorem mixedHighestCoefficient_edge_scaled (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n r b : ℕ)
    (t : occupationWeights (Fin (n+1)) r) (i : Fin n) (hi : 0<t.val i.succ) :
    q^(simpleOccupationWeight n t.val i)*qInteger q (t.val i.castSucc+1)*
        mixedHighestCoefficient q n r b (raisedOccupation n r t i hi)=
      -q^((b:ℤ)*(if i.succ=Fin.last n then 1 else 0))*qInteger q (t.val i.succ)*mixedHighestCoefficient q n r b t := by
  have hw := occupationCompactWeight_raised q hq hq1 n r t i hi
  have hsign : (-1:ℝ)^(occupationHeightZ n r (raisedOccupation n r t i hi))= -(-1:ℝ)^(occupationHeightZ n r t) := by
    rw [raisedOccupation_heightZ,zpow_sub₀ (by norm_num : (-1:ℝ)≠0),zpow_one]
    ring
  have hpow : -(b:ℤ)*(raisedOccupation n r t i hi).val (Fin.last n)=
      (b:ℤ)*(if i.succ=Fin.last n then 1 else 0)+(-(b:ℤ)*t.val (Fin.last n)) := by
    rw [raisedOccupation_last]
    ring
  unfold mixedHighestCoefficient
  rw [hsign,hpow,zpow_add₀ (ne_of_gt hq)]
  have hw0 := ne_of_gt (occupationCompactWeight_pos q hq n r t)
  have hw1 := ne_of_gt (occupationCompactWeight_pos q hq n r (raisedOccupation n r t i hi))
  field_simp [hw0,hw1]
  linear_combination hw

end AMSPhysical
#print axioms AMSPhysical.mixedHighestCoefficient_edge_scaled
