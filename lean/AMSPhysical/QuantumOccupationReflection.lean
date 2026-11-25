import QuantumOppositeWeight
import Mathlib.Data.Fin.Rev

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

def occupationReflection (n L : ℕ) (x : occupationWeights (Fin (n+1)) L) : occupationWeights (Fin (n+1)) L :=
  ⟨fun k =>x.val k.rev,by
    constructor
    · intro k
      exact x.property.1 k.rev
    · rw [show (∑ k : Fin (n+1),x.val k.rev)=∑ k : Fin (n+1),x.val k from Equiv.sum_comp Fin.revPerm x.val]
      exact x.property.2⟩

theorem occupationReflection_involutive (n L : ℕ) : Function.Involutive (occupationReflection n L) := by
  intro x
  apply Subtype.ext
  funext k
  change x.val k.rev.rev=x.val k
  rw [Fin.rev_rev]

def occupationReflectionEquiv (n L : ℕ) : Equiv.Perm (occupationWeights (Fin (n+1)) L) :=
  (occupationReflection_involutive n L).toPerm _

def quantumOccupationReflection (n L : ℕ) :
    quantumOccupationSpace ℝ (Fin (n+1)) L ≃ₗ[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) L :=
  (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).equiv
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L) (occupationReflectionEquiv n L)

theorem quantumOccupationReflection_basis (n L : ℕ) (x : occupationWeights (Fin (n+1)) L) :
    quantumOccupationReflection n L (quantumOccupationBasis (K:=ℝ) L x)=
      quantumOccupationBasis (K:=ℝ) L (occupationReflection n L x) := Module.Basis.equiv_apply _ _ _ _

theorem occupationReflection_square_sum (n L : ℕ) (x : occupationWeights (Fin (n+1)) L) :
    occupationSquareSum (occupationReflection n L x).val=occupationSquareSum x.val :=
  Equiv.sum_comp Fin.revPerm (fun k =>(x.val k)^2)

theorem occupationReflection_energy (n L : ℕ) (x : occupationWeights (Fin (n+1)) L) :
    occupationEnergy n L (occupationReflection n L x)=occupationEnergy n L x := by
  unfold occupationEnergy
  rw [occupationReflection_square_sum]

theorem occupationReflection_height (n L : ℕ) (x : occupationWeights (Fin (n+1)) L) :
    occupationHeightZ n L (occupationReflection n L x)=((n*L:ℕ):ℤ)-occupationHeightZ n L x := by
  have hr : (∑ k : Fin (n+1),(k.val:ℤ)*x.val k.rev)=∑ k : Fin (n+1),(k.rev.val:ℤ)*x.val k := by
    have h := Equiv.sum_comp Fin.revPerm (fun k : Fin (n+1) =>(k.rev.val:ℤ)*x.val k)
    simpa only [Fin.revPerm_apply,Fin.rev_rev] using h
  unfold occupationHeightZ latticePairing
  change (∑ k : Fin (n+1),(k.val:ℤ)*x.val k.rev)=_
  rw [hr]
  have hc : ∀ k : Fin (n+1),(k.rev.val:ℤ)=(n:ℤ)-(k.val:ℤ) := by
    intro k
    have hk:=k.isLt
    simp only [Fin.val_rev]
    omega
  simp_rw [hc,sub_mul]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,x.property.2]
  push_cast
  rfl

theorem occupationReflection_factorial_product (q : ℝ) (n L : ℕ) (x : occupationWeights (Fin (n+1)) L) :
    occupationFactorialProduct q n L (occupationReflection n L x)=occupationFactorialProduct q n L x :=
  Equiv.prod_comp Fin.revPerm (fun k =>qfactorial q ((x.val k).toNat))

/-- Coordinate reversal is an EXACT physical isometry from the compact
symmetric module to its opposite, with no undetermined scalar. -/
theorem occupationReflection_compact_weight (q : ℝ) (hq : q≠0) (n L : ℕ)
    (x : occupationWeights (Fin (n+1)) L) :
    occupationCompactWeight q n L (occupationReflection n L x)=occupationOppositeWeight q n L x := by
  unfold occupationCompactWeight occupationOppositeWeight
  rw [occupationReflection_energy,occupationReflection_height,occupationReflection_factorial_product]
  have he : occupationEnergy n L x+(((n*L:ℕ):ℤ)-occupationHeightZ n L x)=
      ((n*L:ℕ):ℤ)+(occupationEnergy n L x-occupationHeightZ n L x) := by ring
  rw [he,zpow_add₀ hq]

end AMSPhysical
