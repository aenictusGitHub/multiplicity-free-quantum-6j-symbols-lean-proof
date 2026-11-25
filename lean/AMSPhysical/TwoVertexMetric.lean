import TwoVertexEmbedding
import QuantumPureOccupationNorms
import Mathlib.LinearAlgebra.Basis.Bilinear

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2600000
noncomputable section
namespace AMSPhysical

/-- The higher-rank compact metric restricts to the independently
constructed rank-two metric on the actual two-coordinate slice. -/
theorem twoVertexOccupation_weight (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (L : ℕ) (k : Fin (L+1)) :
    occupationCompactWeight q n L (twoVertexOccupation n hn L k)=quantumWeight q L k.val := by
  induction k using Fin.induction with
  | zero =>
    rw [twoVertexOccupation_zero,occupationCompactWeight_highest q hq]
    simpa only [Fin.val_zero] using (quantumWeight_zero q hq L).symm
  | succ j ih =>
    let x := twoVertexOccupation n hn L j.succ
    have hp : 0<x.val (secondVertex n hn) := by
      rw [twoVertexOccupation_second]
      simp only [Fin.val_succ,Nat.cast_add,Nat.cast_one]
      omega
    have hOcc := occupationCompactWeight_raised q hq hq1 n L x (⟨0,hn⟩ : Fin n) hp
    change qInteger q (x.val (secondVertex n hn))*
      occupationCompactWeight q n L (raisedOccupation n L x (⟨0,hn⟩ : Fin n) hp)=
      q^(simpleOccupationWeight n x.val (⟨0,hn⟩ : Fin n))*
        qInteger q (x.val 0+1)*occupationCompactWeight q n L x at hOcc
    have hA : qInteger q (x.val (secondVertex n hn))=qnum q (j.val+1) := by
      dsimp only [x]
      rw [twoVertexOccupation_second]
      exact (qnum_eq_qInteger q hq hq1 (j.val+1)).symm
    have hB : qInteger q (x.val 0+1)=qnum q (L-j.val) := by
      dsimp only [x]
      rw [twoVertexOccupation_first,qnum_eq_qInteger q hq hq1]
      congr 1
      have hj:=j.isLt
      simp only [Fin.val_succ]
      omega
    have hExp : simpleOccupationWeight n x.val (⟨0,hn⟩ : Fin n)=(L:ℤ)-2*((j.val+1:ℕ):ℤ) :=
      twoVertexOccupation_simple n hn L j.succ
    rw [twoVertexOccupation_raised_succ,hA,hB,hExp,ih] at hOcc
    simp only [Fin.coe_castSucc] at hOcc
    have hOld := quantumWeight_step q hq L j.val j.isLt
    have hScalar : qnum q (L-j.val)*q^((L:ℤ)-2*((j.val+1:ℕ):ℤ))≠0 :=
      mul_ne_zero (ne_of_gt (qnum_pos q hq _ (by have hj:=j.isLt;omega))) (zpow_ne_zero _ (ne_of_gt hq))
    have he : (occupationCompactWeight q n L x-quantumWeight q L (j.val+1))*
        (qnum q (L-j.val)*q^((L:ℤ)-2*((j.val+1:ℕ):ℤ)))=0 := by
      linear_combination -hOcc-hOld
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hScalar)

end AMSPhysical
