import FiniteIntegerPrefix
import QuantumNumbers

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical

def qGeometricInteger (q : ℝ) (a : ℤ) : ℝ := q^(1-a)*qInteger q a

theorem qGeometricInteger_zero (q : ℝ) : qGeometricInteger q 0=0 := by simp [qGeometricInteger]

theorem qGeometricInteger_add (q : ℝ) (hq : q≠0) (a b : ℤ) :
    qGeometricInteger q (a+b)=qGeometricInteger q a+q^(-2*a)*qGeometricInteger q b := by
  have hInt : qInteger q (a+b)=q^b*qInteger q a+q^(-a)*qInteger q b := by
    simpa only [add_comm a b] using qInteger_add q hq b a
  have hp1 : q^(1-(a+b))*q^b=q^(1-a) := by
    rw [← zpow_add₀ hq]
    congr 1
    ring
  have hp2 : q^(1-(a+b))*q^(-a)=q^(-2*a)*q^(1-b) := by
    rw [← zpow_add₀ hq,← zpow_add₀ hq]
    congr 1
    ring
  unfold qGeometricInteger
  rw [hInt]
  calc
    _ = (q^(1-(a+b))*q^b)*qInteger q a+(q^(1-(a+b))*q^(-a))*qInteger q b := by ring
    _ = _ := by rw [hp1,hp2];ring

/-- Ordered q-geometric contributions telescope for ARBITRARY integer
increments; no nonnegative occupation assumption or missing boundary occurs. -/
theorem qGeometricInteger_prefix_sum (q : ℝ) (hq : q≠0) (N : ℕ) (x : Fin N → ℤ) :
    (∑ i : Fin N,q^(-2*finiteIntegerPrefix N x i.castSucc)*qGeometricInteger q (x i))=
      qGeometricInteger q (∑ i : Fin N,x i) := by
  calc
    _ = ∑ i : Fin N,(qGeometricInteger q (finiteIntegerPrefix N x i.succ)-
        qGeometricInteger q (finiteIntegerPrefix N x i.castSucc)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [finiteIntegerPrefix_step,qGeometricInteger_add q hq]
      ring
    _ = qGeometricInteger q (finiteIntegerPrefix N x (Fin.last N))-
        qGeometricInteger q (finiteIntegerPrefix N x 0) :=
      fin_sum_adjacent_difference N (fun k =>qGeometricInteger q (finiteIntegerPrefix N x k))
    _ = _ := by rw [finiteIntegerPrefix_last,finiteIntegerPrefix_zero,qGeometricInteger_zero,sub_zero]

end AMSPhysical
