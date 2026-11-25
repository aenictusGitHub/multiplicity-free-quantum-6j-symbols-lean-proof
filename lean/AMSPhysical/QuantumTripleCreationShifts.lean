import QuantumTripleCreation
import QuantumCreationGeneralShift

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

theorem tripleRightCreationCoefficient_middle_shift (q : ℝ) (hq : q≠0) (n : ℕ)
    (i j : Fin (n+1)) (a : ℤ) (p : OccupationTripleLattice n) :
    tripleRightCreationCoefficient q n j (p+(0,Pi.single i a,0))=
      q^(-(if j.val ≤ i.val then a else 0:ℤ))*tripleRightCreationCoefficient q n j p := by
  dsimp only [tripleRightCreationCoefficient,Prod.fst_add,Prod.snd_add]
  rw [add_zero,occupationLatticeReflect_add,occupationLatticeReflect_single_scalar]
  have he : i.rev.val ≤ j.rev.val ↔ j.val ≤ i.val := by simp only [Fin.val_rev];omega
  have h:=mixedCreationCoefficient_first_single_shift q hq n j.rev i.rev a
    (occupationLatticeReflect n p.2.1,occupationLatticeReflect n p.2.2)
  simpa only [he,add_zero,tripleRightCreationCoefficient,mixedCreationCoefficient,Prod.fst_add,Prod.snd_add] using h

theorem tripleRightCreationCoefficient_third_shift (q : ℝ) (hq : q≠0) (n : ℕ)
    (i j : Fin (n+1)) (a : ℤ) (p : OccupationTripleLattice n) :
    tripleRightCreationCoefficient q n j (p+(0,0,Pi.single i a))=
      q^(-(if j.val ≤ i.val then a else 0:ℤ))*tripleRightCreationCoefficient q n j p := by
  dsimp only [tripleRightCreationCoefficient,Prod.fst_add,Prod.snd_add]
  rw [add_zero,occupationLatticeReflect_add,occupationLatticeReflect_single_scalar]
  have he : i.rev.val ≤ j.rev.val ↔ j.val ≤ i.val := by simp only [Fin.val_rev];omega
  have h:=mixedCreationCoefficient_second_single_shift q hq n j.rev i.rev a
    (occupationLatticeReflect n p.2.1,occupationLatticeReflect n p.2.2)
  simpa only [he,add_zero,tripleRightCreationCoefficient,mixedCreationCoefficient,Prod.fst_add,Prod.snd_add] using h

theorem occupationPrefix_last_sum (n : ℕ) (x : Fin (n+1) → ℤ) :
    occupationPrefix n (Fin.last n) x=∑ i : Fin (n+1),x i := by
  unfold occupationPrefix latticePairing
  apply Finset.sum_congr rfl
  intro i hi
  have h : i.val ≤ (Fin.last n).val := by have hh:=i.isLt;simp only [Fin.val_last];omega
  simp only [if_pos h,one_mul]

theorem occupationLatticeReflect_sum (n : ℕ) (x : Fin (n+1) → ℤ) :
    (∑ i : Fin (n+1),occupationLatticeReflect n x i)=∑ i : Fin (n+1),x i :=
  Equiv.sum_comp Fin.revPerm x

theorem tripleRightCreationCoefficient_zero (q : ℝ) (n : ℕ) (p : OccupationTripleLattice n) :
    tripleRightCreationCoefficient q n 0 p=
      (-1:ℝ)^n*q^(-(n:ℤ)-(∑ i : Fin (n+1),p.2.1 i)-(∑ i : Fin (n+1),p.2.2 i)) := by
  unfold tripleRightCreationCoefficient mixedCreationCoefficient
  rw [Fin.rev_zero]
  simp only [Fin.val_last]
  rw [occupationPrefix_last_sum,occupationPrefix_last_sum,occupationLatticeReflect_sum,occupationLatticeReflect_sum]

end AMSPhysical
