import QuantumOccupationPrefix
import QuantumPairRaising

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical

def mixedCreationShift (n : ℕ) (k : Fin (n+1)) : OccupationPairLattice n := (Pi.single k 1,Pi.single k 1)

def mixedCreationCoefficient (q : ℝ) (n : ℕ) (k : Fin (n+1)) (p : OccupationPairLattice n) : ℝ :=
  (-1:ℝ)^k.val*q^(-(k.val:ℤ)-occupationPrefix n k p.1-occupationPrefix n k p.2)

theorem mixedCreationCoefficient_first_root (q : ℝ) (hq : q≠0) (n : ℕ) (k : Fin (n+1))
    (i : Fin n) (p : OccupationPairLattice n) :
    mixedCreationCoefficient q n k (p+(latticeRoot i.castSucc i.succ,0))=
      q^(-(if k=i.castSucc then 1 else 0:ℤ))*mixedCreationCoefficient q n k p := by
  unfold mixedCreationCoefficient
  change (-1:ℝ)^k.val*q^(-(k.val:ℤ)-occupationPrefix n k (p.1+latticeRoot i.castSucc i.succ)-occupationPrefix n k (p.2+0))=_
  rw [add_zero,occupationPrefix_add,occupationPrefix_root]
  have he : -(k.val:ℤ)-(occupationPrefix n k p.1+(if k=i.castSucc then 1 else 0:ℤ))-occupationPrefix n k p.2=
      (-(if k=i.castSucc then 1 else 0:ℤ))+(-(k.val:ℤ)-occupationPrefix n k p.1-occupationPrefix n k p.2) := by ring
  rw [he,zpow_add₀ hq]
  ring

theorem mixedCreationCoefficient_second_negative_root (q : ℝ) (hq : q≠0) (n : ℕ) (k : Fin (n+1))
    (i : Fin n) (p : OccupationPairLattice n) :
    mixedCreationCoefficient q n k (p+(0,-latticeRoot i.castSucc i.succ))=
      q^(if k=i.castSucc then 1 else 0:ℤ)*mixedCreationCoefficient q n k p := by
  unfold mixedCreationCoefficient
  change (-1:ℝ)^k.val*q^(-(k.val:ℤ)-occupationPrefix n k (p.1+0)-occupationPrefix n k (p.2+ -latticeRoot i.castSucc i.succ))=_
  rw [add_zero,occupationPrefix_add,occupationPrefix_neg,occupationPrefix_root]
  have he : -(k.val:ℤ)-occupationPrefix n k p.1-(occupationPrefix n k p.2+ -(if k=i.castSucc then 1 else 0:ℤ))=
      (if k=i.castSucc then 1 else 0:ℤ)+(-(k.val:ℤ)-occupationPrefix n k p.1-occupationPrefix n k p.2) := by ring
  rw [he,zpow_add₀ hq]
  ring

theorem mixedCreationCoefficient_adjacent (q : ℝ) (hq : q≠0) (n : ℕ) (i : Fin n) (p : OccupationPairLattice n) :
    mixedCreationCoefficient q n i.castSucc p+
      q^(p.1 i.succ+p.2 i.succ+1)*mixedCreationCoefficient q n i.succ p=0 := by
  have hp : q^(p.1 i.succ+p.2 i.succ+1)*
      q^(-((i.val:ℤ)+1)-(occupationPrefix n i.castSucc p.1+p.1 i.succ)-
        (occupationPrefix n i.castSucc p.2+p.2 i.succ))=
      q^(-(i.val:ℤ)-occupationPrefix n i.castSucc p.1-occupationPrefix n i.castSucc p.2) := by
    rw [← zpow_add₀ hq]
    congr 1
    ring
  unfold mixedCreationCoefficient
  rw [occupationPrefix_succ,occupationPrefix_succ]
  simp only [Fin.coe_castSucc,Fin.val_succ,Nat.cast_add,Nat.cast_one,pow_succ]
  linear_combination -((-1:ℝ)^i.val)*hp

def pairLatticeCreation (q : ℝ) (n : ℕ) : Module.End ℝ (OccupationPairLattice n →₀ ℝ) :=
  ∑ k : Fin (n+1),weightedTranslation (mixedCreationShift n k) (mixedCreationCoefficient q n k)

end AMSPhysical
