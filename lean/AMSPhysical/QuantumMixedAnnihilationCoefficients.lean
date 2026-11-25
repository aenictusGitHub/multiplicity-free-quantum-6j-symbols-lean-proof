import QuantumStrictPrefix
import QuantumMixedCreationCoefficients
import WeightedTranslationScalar

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical

def mixedAnnihilationCoefficient (q : ℝ) (n : ℕ) (i : Fin (n+1)) (p : OccupationPairLattice n) : ℝ :=
  (-1:ℝ)^i.val*q^(-(i.val:ℤ)-occupationStrictPrefix n i p.1-occupationStrictPrefix n i p.2)*
    qInteger q (p.1 i)*qInteger q (p.2 i)

def pairLatticeAnnihilation (q : ℝ) (n : ℕ) : Module.End ℝ (OccupationPairLattice n →₀ ℝ) :=
  ∑ i : Fin (n+1),weightedTranslation (-mixedCreationShift n i) (mixedAnnihilationCoefficient q n i)

theorem mixedCreationCoefficient_creation_shift (q : ℝ) (hq : q≠0) (n : ℕ)
    (i j : Fin (n+1)) (p : OccupationPairLattice n) :
    mixedCreationCoefficient q n i (p+mixedCreationShift n j)=
      q^(-2*(if j.val≤ i.val then 1 else 0:ℤ))*mixedCreationCoefficient q n i p := by
  unfold mixedCreationCoefficient mixedCreationShift
  change (-1:ℝ)^i.val*q^(-(i.val:ℤ)-occupationPrefix n i (p.1+Pi.single j 1)-
    occupationPrefix n i (p.2+Pi.single j 1))=_
  simp only [occupationPrefix_add,occupationPrefix_single]
  have he : -(i.val:ℤ)-(occupationPrefix n i p.1+(if j.val≤ i.val then 1 else 0:ℤ))-
      (occupationPrefix n i p.2+(if j.val≤ i.val then 1 else 0:ℤ))=
      -2*(if j.val≤ i.val then 1 else 0:ℤ)+(-(i.val:ℤ)-occupationPrefix n i p.1-occupationPrefix n i p.2) := by ring
  rw [he,zpow_add₀ hq]
  ring

theorem mixedCreationCoefficient_annihilation_shift (q : ℝ) (hq : q≠0) (n : ℕ)
    (i j : Fin (n+1)) (p : OccupationPairLattice n) :
    mixedCreationCoefficient q n i (p-mixedCreationShift n j)=
      q^(2*(if j.val≤ i.val then 1 else 0:ℤ))*mixedCreationCoefficient q n i p := by
  unfold mixedCreationCoefficient mixedCreationShift
  change (-1:ℝ)^i.val*q^(-(i.val:ℤ)-occupationPrefix n i (p.1-Pi.single j 1)-
    occupationPrefix n i (p.2-Pi.single j 1))=_
  simp only [sub_eq_add_neg,occupationPrefix_add,occupationPrefix_neg,occupationPrefix_single]
  have he : -(i.val:ℤ)+ -(occupationPrefix n i p.1+ -(if j.val≤ i.val then 1 else 0:ℤ))+
      -(occupationPrefix n i p.2+ -(if j.val≤ i.val then 1 else 0:ℤ))=
      2*(if j.val≤ i.val then 1 else 0:ℤ)+(-(i.val:ℤ)+ -occupationPrefix n i p.1+ -occupationPrefix n i p.2) := by ring
  rw [he,zpow_add₀ hq]
  ring

theorem mixedAnnihilationCoefficient_other_creation (q : ℝ) (hq : q≠0) (n : ℕ)
    (i j : Fin (n+1)) (hij : i≠j) (p : OccupationPairLattice n) :
    mixedAnnihilationCoefficient q n i (p+mixedCreationShift n j)=
      q^(-2*(if j.val < i.val then 1 else 0:ℤ))*mixedAnnihilationCoefficient q n i p := by
  unfold mixedAnnihilationCoefficient mixedCreationShift
  change (-1:ℝ)^i.val*q^(-(i.val:ℤ)-occupationStrictPrefix n i (p.1+Pi.single j 1)-
    occupationStrictPrefix n i (p.2+Pi.single j 1))*
    qInteger q ((p.1+Pi.single j 1 : Fin (n+1) → ℤ) i)*
    qInteger q ((p.2+Pi.single j 1 : Fin (n+1) → ℤ) i)=_
  simp only [occupationStrictPrefix_add,occupationStrictPrefix_single,Pi.add_apply,Pi.single_apply,
    if_neg hij,if_neg (Ne.symm hij),add_zero]
  have he : -(i.val:ℤ)-(occupationStrictPrefix n i p.1+(if j.val < i.val then 1 else 0:ℤ))-
      (occupationStrictPrefix n i p.2+(if j.val < i.val then 1 else 0:ℤ))=
      -2*(if j.val < i.val then 1 else 0:ℤ)+(-(i.val:ℤ)-occupationStrictPrefix n i p.1-occupationStrictPrefix n i p.2) := by ring
  rw [he,zpow_add₀ hq]
  ring

end AMSPhysical
