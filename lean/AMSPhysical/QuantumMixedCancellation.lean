import QuantumMixedCoefficient

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

theorem mixedHighestCoefficient_cancellation (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n r b : ℕ)
    (t : occupationWeights (Fin (n+1)) r) (i : Fin n) (hi : 0<t.val i.succ) :
    mixedHighestCoefficient q n r b t*qInteger q (t.val i.succ)*
        q^(-simpleOccupationWeight n t.val i+(b:ℤ)*(if i.succ=Fin.last n then 1 else 0))+
      mixedHighestCoefficient q n r b (raisedOccupation n r t i hi)*qInteger q (t.val i.castSucc+1)=0 := by
  have he := mixedHighestCoefficient_edge_scaled q hq hq1 n r b t i hi
  have hp : q^(simpleOccupationWeight n t.val i)*
      q^(-simpleOccupationWeight n t.val i+(b:ℤ)*(if i.succ=Fin.last n then 1 else 0))=
      q^((b:ℤ)*(if i.succ=Fin.last n then 1 else 0)) := by
    rw [← zpow_add₀ (ne_of_gt hq)]
    congr 1
    ring
  apply (mul_eq_zero.mp (show q^(simpleOccupationWeight n t.val i)*
      (mixedHighestCoefficient q n r b t*qInteger q (t.val i.succ)*
        q^(-simpleOccupationWeight n t.val i+(b:ℤ)*(if i.succ=Fin.last n then 1 else 0))+
      mixedHighestCoefficient q n r b (raisedOccupation n r t i hi)*qInteger q (t.val i.castSucc+1))=0 from ?_)).resolve_left
      (zpow_ne_zero _ (ne_of_gt hq))
  calc
    _ = (q^(simpleOccupationWeight n t.val i)*q^(-simpleOccupationWeight n t.val i+
      (b:ℤ)*(if i.succ=Fin.last n then 1 else 0)))*qInteger q (t.val i.succ)*mixedHighestCoefficient q n r b t+
      q^(simpleOccupationWeight n t.val i)*qInteger q (t.val i.castSucc+1)*
        mixedHighestCoefficient q n r b (raisedOccupation n r t i hi) := by ring
    _ = _ := by rw [hp,he];ring

end AMSPhysical
#print axioms AMSPhysical.mixedHighestCoefficient_cancellation
