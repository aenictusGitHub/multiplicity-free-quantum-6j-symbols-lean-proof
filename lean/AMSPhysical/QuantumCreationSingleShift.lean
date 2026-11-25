import QuantumMixedCreationCoefficients

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

theorem mixedCreationCoefficient_first_unit_shift (q : ℝ) (hq : q≠0) (n : ℕ)
    (i j : Fin (n+1)) (p : OccupationPairLattice n) :
    mixedCreationCoefficient q n i (p+(Pi.single j 1,0))=
      q^(-(if j.val ≤ i.val then 1 else 0:ℤ))*mixedCreationCoefficient q n i p := by
  unfold mixedCreationCoefficient
  change (-1:ℝ)^i.val*q^(-(i.val:ℤ)-occupationPrefix n i (p.1+Pi.single j 1)-occupationPrefix n i (p.2+0))=_
  rw [add_zero]
  simp only [occupationPrefix_add,occupationPrefix_single]
  have he : -(i.val:ℤ)-(occupationPrefix n i p.1+(if j.val ≤ i.val then 1 else 0:ℤ))-occupationPrefix n i p.2=
      (-(if j.val ≤ i.val then 1 else 0:ℤ))+(-(i.val:ℤ)-occupationPrefix n i p.1-occupationPrefix n i p.2) := by ring
  rw [he,zpow_add₀ hq]
  ring

theorem mixedCreationCoefficient_second_unit_shift (q : ℝ) (hq : q≠0) (n : ℕ)
    (i j : Fin (n+1)) (p : OccupationPairLattice n) :
    mixedCreationCoefficient q n i (p+(0,Pi.single j 1))=
      q^(-(if j.val ≤ i.val then 1 else 0:ℤ))*mixedCreationCoefficient q n i p := by
  unfold mixedCreationCoefficient
  change (-1:ℝ)^i.val*q^(-(i.val:ℤ)-occupationPrefix n i (p.1+0)-occupationPrefix n i (p.2+Pi.single j 1))=_
  rw [add_zero]
  simp only [occupationPrefix_add,occupationPrefix_single]
  have he : -(i.val:ℤ)-occupationPrefix n i p.1-(occupationPrefix n i p.2+(if j.val ≤ i.val then 1 else 0:ℤ))=
      (-(if j.val ≤ i.val then 1 else 0:ℤ))+(-(i.val:ℤ)-occupationPrefix n i p.1-occupationPrefix n i p.2) := by ring
  rw [he,zpow_add₀ hq]
  ring

end AMSPhysical
