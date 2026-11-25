import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Trace

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

def finiteIntegerPrefix (N : ℕ) (x : Fin N → ℤ) (k : Fin (N+1)) : ℤ :=
  ∑ j : Fin N,if j.val < k.val then x j else 0

theorem finiteIntegerPrefix_zero (N : ℕ) (x : Fin N → ℤ) : finiteIntegerPrefix N x 0=0 := by
  simp [finiteIntegerPrefix]

theorem finiteIntegerPrefix_last (N : ℕ) (x : Fin N → ℤ) :
    finiteIntegerPrefix N x (Fin.last N)=∑ j : Fin N,x j := by
  unfold finiteIntegerPrefix
  apply Finset.sum_congr rfl
  intro j hj
  exact if_pos j.isLt

theorem finiteIntegerPrefix_step (N : ℕ) (x : Fin N → ℤ) (i : Fin N) :
    finiteIntegerPrefix N x i.succ=finiteIntegerPrefix N x i.castSucc+x i := by
  have he : ∀ j : Fin N,(if j.val < i.succ.val then x j else 0)=
      (if j.val < i.castSucc.val then x j else 0)+(if j=i then x j else 0) := by
    intro j
    simp only [Fin.val_succ,Fin.coe_castSucc,Fin.ext_iff]
    split_ifs <;> omega
  unfold finiteIntegerPrefix
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem finiteIntegerPrefix_add (N : ℕ) (x y : Fin N → ℤ) (k : Fin (N+1)) :
    finiteIntegerPrefix N (x+y) k=finiteIntegerPrefix N x k+finiteIntegerPrefix N y k := by
  unfold finiteIntegerPrefix
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Pi.add_apply]
  split_ifs <;> ring

theorem finiteIntegerPrefix_neg (N : ℕ) (x : Fin N → ℤ) (k : Fin (N+1)) :
    finiteIntegerPrefix N (-x) k= -finiteIntegerPrefix N x k := by
  unfold finiteIntegerPrefix
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Pi.neg_apply]
  split_ifs <;> ring

theorem finiteIntegerPrefix_single (N : ℕ) (i : Fin N) (k : Fin (N+1)) :
    finiteIntegerPrefix N (Pi.single i 1) k=(if i.val < k.val then 1 else 0) := by
  unfold finiteIntegerPrefix
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [Pi.single_apply,hji,Ne.symm hji]
  · simp

theorem finiteIntegerPrefix_one (N : ℕ) (k : Fin (N+1)) :
    finiteIntegerPrefix N (fun _ =>1) k=(k.val:ℤ) := by
  induction k using Fin.induction with
  | zero => rw [finiteIntegerPrefix_zero];rfl
  | succ i ih => rw [finiteIntegerPrefix_step,ih];simp

theorem fin_sum_adjacent_difference {K : Type*} [AddCommGroup K] (N : ℕ) (f : Fin (N+1) → K) :
    (∑ i : Fin N,(f i.succ-f i.castSucc))=f (Fin.last N)-f 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Fin.sum_univ_succ]
    have he:=ih (fun i : Fin (N+1) =>f i.succ)
    simp only [Fin.succ_castSucc] at he
    rw [he]
    simp only [Fin.succ_last,Fin.castSucc_zero]
    abel

end AMSPhysical
