import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace AMSPhysical

theorem minimumDiagonalSum_invert_succ (P : ℕ → ℝ) (D : ℕ → ℕ → ℝ)
    (h : ∀ a b,P a*P b=∑ r : Fin (min a b+1),D (a-r.val) (b-r.val)) (a b : ℕ) :
    D (a+1) (b+1)=P (a+1)*P (b+1)-P a*P b := by
  have h1:=h (a+1) (b+1)
  have h0:=h a b
  have hm : min (a+1) (b+1)=min a b+1 := by omega
  rw [hm,Fin.sum_univ_succ] at h1
  simp only [Fin.val_zero,Fin.val_succ,Nat.sub_zero,Nat.add_sub_add_right] at h1
  rw [← h0] at h1
  linarith

theorem minimumDiagonalSum_left_zero (P : ℕ → ℝ) (D : ℕ → ℕ → ℝ)
    (h : ∀ a b,P a*P b=∑ r : Fin (min a b+1),D (a-r.val) (b-r.val)) (b : ℕ) :
    D 0 b=P 0*P b := by
  have hh:=h 0 b
  rw [Nat.zero_min,zero_add,Fin.sum_univ_one] at hh
  simpa only [Fin.val_zero,Nat.sub_zero] using hh.symm

theorem minimumDiagonalSum_right_zero (P : ℕ → ℝ) (D : ℕ → ℕ → ℝ)
    (h : ∀ a b,P a*P b=∑ r : Fin (min a b+1),D (a-r.val) (b-r.val)) (a : ℕ) :
    D a 0=P a*P 0 := by
  have hh:=h a 0
  rw [Nat.min_zero,zero_add,Fin.sum_univ_one] at hh
  simpa only [Fin.val_zero,Nat.sub_zero] using hh.symm

end AMSPhysical
