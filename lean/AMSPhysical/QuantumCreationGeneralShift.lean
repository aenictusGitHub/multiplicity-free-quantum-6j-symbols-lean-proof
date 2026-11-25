import QuantumCreationSingleShift
import QuantumLatticeReflectSingle

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 180000
noncomputable section
namespace AMSPhysical

theorem occupationPrefix_single_scalar (n : ℕ) (i j : Fin (n+1)) (a : ℤ) :
    occupationPrefix n i (Pi.single j a)=(if j.val ≤ i.val then a else 0) := by
  simp [occupationPrefix,latticePairing,Pi.single_apply,mul_ite]

theorem occupationLatticeReflect_single_scalar (n : ℕ) (i : Fin (n+1)) (a : ℤ) :
    occupationLatticeReflect n (Pi.single i a)=Pi.single i.rev a := by
  funext k
  simp only [occupationLatticeReflect,Pi.single_apply,Fin.rev_eq_iff]

theorem mixedCreationCoefficient_first_single_shift (q : ℝ) (hq : q≠0) (n : ℕ)
    (i j : Fin (n+1)) (a : ℤ) (p : OccupationPairLattice n) :
    mixedCreationCoefficient q n i (p+(Pi.single j a,0))=
      q^(-(if j.val ≤ i.val then a else 0:ℤ))*mixedCreationCoefficient q n i p := by
  unfold mixedCreationCoefficient
  simp only [Prod.fst_add,Prod.snd_add,add_zero]
  rw [occupationPrefix_add,occupationPrefix_single_scalar]
  have he : -(i.val:ℤ)-(occupationPrefix n i p.1+(if j.val ≤ i.val then a else 0:ℤ))-occupationPrefix n i p.2=
      (-(if j.val ≤ i.val then a else 0:ℤ))+(-(i.val:ℤ)-occupationPrefix n i p.1-occupationPrefix n i p.2) := by ring
  rw [he,zpow_add₀ hq]
  ring

theorem mixedCreationCoefficient_second_single_shift (q : ℝ) (hq : q≠0) (n : ℕ)
    (i j : Fin (n+1)) (a : ℤ) (p : OccupationPairLattice n) :
    mixedCreationCoefficient q n i (p+(0,Pi.single j a))=
      q^(-(if j.val ≤ i.val then a else 0:ℤ))*mixedCreationCoefficient q n i p := by
  unfold mixedCreationCoefficient
  simp only [Prod.fst_add,Prod.snd_add,add_zero]
  rw [occupationPrefix_add,occupationPrefix_single_scalar]
  have he : -(i.val:ℤ)-occupationPrefix n i p.1-(occupationPrefix n i p.2+(if j.val ≤ i.val then a else 0:ℤ))=
      (-(if j.val ≤ i.val then a else 0:ℤ))+(-(i.val:ℤ)-occupationPrefix n i p.1-occupationPrefix n i p.2) := by ring
  rw [he,zpow_add₀ hq]
  ring

end AMSPhysical
