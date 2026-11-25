import QuantumOccupationPrefix
import FiniteIntegerPrefix

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

def occupationStrictPrefix (n : ℕ) (i : Fin (n+1)) (x : Fin (n+1) → ℤ) : ℤ :=
  finiteIntegerPrefix (n+1) x i.castSucc

theorem occupationPrefix_eq_finite (n : ℕ) (i : Fin (n+1)) (x : Fin (n+1) → ℤ) :
    occupationPrefix n i x=finiteIntegerPrefix (n+1) x i.succ := by
  unfold occupationPrefix latticePairing finiteIntegerPrefix
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Fin.val_succ]
  by_cases h : j.val≤ i.val
  · have h' : j.val < i.val+1 := by omega
    simp only [if_pos h,if_pos h',one_mul]
  · have h' : ¬ j.val < i.val+1 := by omega
    simp only [if_neg h,if_neg h',zero_mul]

theorem occupationPrefix_strict (n : ℕ) (i : Fin (n+1)) (x : Fin (n+1) → ℤ) :
    occupationPrefix n i x=occupationStrictPrefix n i x+x i := by
  rw [occupationPrefix_eq_finite,finiteIntegerPrefix_step]
  rfl

theorem occupationStrictPrefix_add (n : ℕ) (i : Fin (n+1)) (x y : Fin (n+1) → ℤ) :
    occupationStrictPrefix n i (x+y)=occupationStrictPrefix n i x+occupationStrictPrefix n i y :=
  finiteIntegerPrefix_add _ _ _ _

theorem occupationStrictPrefix_neg (n : ℕ) (i : Fin (n+1)) (x : Fin (n+1) → ℤ) :
    occupationStrictPrefix n i (-x)= -occupationStrictPrefix n i x :=
  finiteIntegerPrefix_neg _ _ _

theorem occupationStrictPrefix_single (n : ℕ) (i j : Fin (n+1)) :
    occupationStrictPrefix n i (Pi.single j 1)=(if j.val < i.val then 1 else 0) :=
  finiteIntegerPrefix_single _ _ _

theorem occupationStrictPrefix_self_single (n : ℕ) (i : Fin (n+1)) :
    occupationStrictPrefix n i (Pi.single i 1)=0 := by
  rw [occupationStrictPrefix_single,if_neg (lt_irrefl i.val)]

end AMSPhysical
