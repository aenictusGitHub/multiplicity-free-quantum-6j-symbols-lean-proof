import QuantumTypeAWeights

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

def occupationPrefix (n : ℕ) (k : Fin (n+1)) (x : Fin (n+1) → ℤ) : ℤ :=
  latticePairing (fun j : Fin (n+1) =>if j.val≤k.val then 1 else 0) x

theorem occupationPrefix_add (n : ℕ) (k : Fin (n+1)) (x y : Fin (n+1) → ℤ) :
    occupationPrefix n k (x+y)=occupationPrefix n k x+occupationPrefix n k y :=
  latticePairing_add_right _ _ _

theorem occupationPrefix_neg (n : ℕ) (k : Fin (n+1)) (x : Fin (n+1) → ℤ) :
    occupationPrefix n k (-x)= -occupationPrefix n k x := by
  simp only [occupationPrefix,latticePairing,Pi.neg_apply,mul_neg,Finset.sum_neg_distrib]

theorem occupationPrefix_root (n : ℕ) (k : Fin (n+1)) (i : Fin n) :
    occupationPrefix n k (latticeRoot i.castSucc i.succ)=(if k=i.castSucc then 1 else 0) := by
  unfold occupationPrefix
  rw [latticePairing_root_right]
  simp only [Fin.coe_castSucc,Fin.val_succ,Fin.ext_iff]
  split_ifs <;> omega

theorem occupationPrefix_single (n : ℕ) (k j : Fin (n+1)) :
    occupationPrefix n k (Pi.single j 1)=(if j.val≤k.val then 1 else 0) := by
  simp [occupationPrefix,latticePairing,Pi.single_apply,mul_ite]

theorem occupationPrefix_succ (n : ℕ) (i : Fin n) (x : Fin (n+1) → ℤ) :
    occupationPrefix n i.succ x=occupationPrefix n i.castSucc x+x i.succ := by
  have h : (fun j : Fin (n+1) =>if j.val ≤ i.succ.val then (1:ℤ) else 0)=
      (fun j : Fin (n+1) =>if j.val ≤ i.castSucc.val then (1:ℤ) else 0)+Pi.single i.succ 1 := by
    funext j
    simp only [Pi.add_apply,Pi.single_apply,Fin.ext_iff,Fin.coe_castSucc,Fin.val_succ]
    split_ifs <;> omega
  unfold occupationPrefix
  rw [h,latticePairing_add_left]
  congr 1
  simp [latticePairing,Pi.single_apply,ite_mul]

end AMSPhysical
