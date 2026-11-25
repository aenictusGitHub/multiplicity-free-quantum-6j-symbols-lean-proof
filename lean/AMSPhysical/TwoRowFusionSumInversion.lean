import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
namespace AMSPhysical

theorem twoRowFusionSum_invert_succ (P : ℕ → ℝ) (D : ℕ → ℕ → ℝ)
    (h : ∀ l m,P l*P m=∑ r : Fin (min l m+1),D (l+m-2*r.val) r.val) (a b : ℕ) :
    D a (b+1)=P (a+b+1)*P (b+1)-P (a+b+2)*P b := by
  have h1:=h (a+b+1) (b+1)
  have h0:=h (a+b+2) b
  rw [show min (a+b+1) (b+1)=b+1 from by omega,Fin.sum_univ_castSucc] at h1
  rw [show min (a+b+2) b=b from by omega] at h0
  simp only [Fin.coe_castSucc,Fin.val_last] at h1
  have he : (∑ r : Fin (b+1),D ((a+b+1)+(b+1)-2*r.val) r.val)=
      ∑ r : Fin (b+1),D ((a+b+2)+b-2*r.val) r.val := by
    apply Finset.sum_congr rfl
    intro r _
    congr 2 <;> omega
  rw [he,← h0,show a+b+1+(b+1)-2*(b+1)=a from by omega] at h1
  linarith

theorem twoRowFusionSum_right_zero (P : ℕ → ℝ) (D : ℕ → ℕ → ℝ)
    (h : ∀ l m,P l*P m=∑ r : Fin (min l m+1),D (l+m-2*r.val) r.val) (a : ℕ) :
    D a 0=P a*P 0 := by
  have hh:=h a 0
  rw [Nat.min_zero,zero_add,Fin.sum_univ_one] at hh
  simpa only [Fin.val_zero,mul_zero,Nat.add_zero,Nat.sub_zero] using hh.symm

end AMSPhysical
#print axioms AMSPhysical.twoRowFusionSum_invert_succ
