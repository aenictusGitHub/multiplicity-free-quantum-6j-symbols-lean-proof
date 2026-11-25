import QuantumOccupationEnergy
import QuantumOccupationLowering

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

def shiftedOccupation (n r a : ℕ) (k : Fin (n+1)) (x : occupationWeights (Fin (n+1)) r) :
    occupationWeights (Fin (n+1)) (r+a) :=
  ⟨x.val+Pi.single k (a:ℤ),by
    constructor
    · intro j
      change 0≤x.val j+(Pi.single k (a:ℤ) : Fin (n+1) → ℤ) j
      have hx := x.property.1 j
      simp only [Pi.single_apply]
      split_ifs <;> omega
    · simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib,x.property.2]
      simp⟩

theorem shiftedOccupation_injective (n r a : ℕ) (k : Fin (n+1)) :
    Function.Injective (shiftedOccupation n r a k) := by
  intro x y he
  apply Subtype.ext
  have hh := congrArg Subtype.val he
  change x.val+Pi.single k (a:ℤ)=y.val+Pi.single k (a:ℤ) at hh
  exact add_right_cancel hh

theorem shiftedOccupation_high_source (n r a : ℕ) (x : occupationWeights (Fin (n+1)) r) (i : Fin n) :
    (shiftedOccupation n r a 0 x).val i.succ=x.val i.succ := by
  have hi : i.succ≠(0:Fin (n+1)) := by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_succ,Fin.val_zero] at hh
    omega
  simp [shiftedOccupation,Pi.single_apply,hi,Ne.symm hi]

theorem shiftedOccupation_low_target (n r b : ℕ) (x : occupationWeights (Fin (n+1)) r) (i : Fin n) :
    (shiftedOccupation n r b (Fin.last n) x).val i.castSucc=x.val i.castSucc := by
  have hi : i.castSucc≠Fin.last n := by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.coe_castSucc,Fin.val_last] at hh
    exact (Nat.ne_of_lt i.isLt) hh
  simp [shiftedOccupation,Pi.single_apply,hi,Ne.symm hi]

theorem raisedOccupation_last (n r : ℕ) (x : occupationWeights (Fin (n+1)) r)
    (i : Fin n) (hi : 0<x.val i.succ) :
    (raisedOccupation n r x i hi).val (Fin.last n)=
      x.val (Fin.last n)-(if i.succ=Fin.last n then 1 else 0) := by
  have ha : i.castSucc≠Fin.last n := by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.coe_castSucc,Fin.val_last] at hh
    exact (Nat.ne_of_lt i.isLt) hh
  change (x.val+latticeRoot i.castSucc i.succ) (Fin.last n)=_
  simp only [Pi.add_apply,latticeRoot,Pi.sub_apply,Pi.single_apply]
  by_cases hb : i.succ=Fin.last n
  · simp [ha,Ne.symm ha,hb]
    ring
  · simp [ha,Ne.symm ha,hb,Ne.symm hb]

end AMSPhysical
#print axioms AMSPhysical.raisedOccupation_last
