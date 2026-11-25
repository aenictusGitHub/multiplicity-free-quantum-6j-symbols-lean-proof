import QuantumMixedCreationIntertwiner
import QuantumCreationBoundary
import MixedFusionHighestUnique

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def mixedFusionIndexSucc (l m : ℕ) (r : MixedFusionIndex l m) : MixedFusionIndex (l+1) (m+1) :=
  ⟨r.val+1,by have hr:=r.isLt;omega⟩

theorem mixedBoundaryAt_succ (n l m : ℕ) (r : MixedFusionIndex l m) :
    (mixedBoundaryAt n (l+1) (m+1) (mixedFusionIndexSucc l m r)).val=
      (mixedBoundaryAt n l m r).val+Pi.single 0 1 := by
  change (Pi.single 0 ((r.val+1:ℕ):ℤ)+Pi.single (Fin.last n) ((m+1-(r.val+1):ℕ):ℤ) : Fin (n+1) → ℤ)=_
  rw [Nat.add_sub_add_right]
  change (Pi.single 0 ((r.val+1:ℕ):ℤ)+Pi.single (Fin.last n) ((m-r.val:ℕ):ℤ) : Fin (n+1) → ℤ)=
    (Pi.single 0 (r.val:ℤ)+Pi.single (Fin.last n) ((m-r.val:ℕ):ℤ) : Fin (n+1) → ℤ)+Pi.single 0 1
  ext k
  simp only [Pi.add_apply,Pi.single_apply,Nat.cast_add,Nat.cast_one]
  split_ifs <;> ring

theorem mixedFiniteCreation_highest_boundary (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n)
    (l m : ℕ) (r : MixedFusionIndex l m) :
    mixedBoundaryFunctional n (l+1) (m+1) (mixedFusionIndexSucc l m r)
      (mixedFiniteCreation q n l m (mixedFusionHighestAt q n l m r))=q^(-(l:ℤ)-(r.val:ℤ)) := by
  change occupationTensorCoefficients n (l+1) (m+1) (mixedFiniteCreation q n l m (mixedFusionHighestAt q n l m r))
    ((highestOccupation n (l+1)).val,(mixedBoundaryAt n (l+1) (m+1) (mixedFusionIndexSucc l m r)).val)=_
  rw [mixedBoundaryAt_succ,occupationTensorCoefficients_creation_boundary,
    mixedFusionHighestAt_boundary q hq n hn,if_pos rfl,mul_one]
  rw [show (mixedBoundaryAt n l m r).val 0=(r.val:ℤ) from mixedBoundaryOccupation_first n m r.val hn _]

/-- The actual creation map has the explicit, nonzero leading coefficient
on each physical channel; highest-line uniqueness determines the whole vector. -/
theorem mixedFiniteCreation_highest (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n : ℕ) (hn : 0<n)
    (l m : ℕ) (r : MixedFusionIndex l m) :
    mixedFiniteCreation q n l m (mixedFusionHighestAt q n l m r)=
      q^(-(l:ℤ)-(r.val:ℤ)) • mixedFusionHighestAt q n (l+1) (m+1) (mixedFusionIndexSucc l m r) := by
  rw [← mixedFiniteCreation_highest_boundary q hq n hn l m r]
  apply mixedFusionHighestAt_full_weight_unique q hq hq1 n hn (l+1) (m+1) (mixedFusionIndexSucc l m r)
  · intro i
    rw [← mixedFiniteCreation_intertwines_E,mixedFusionHighestAt_E_zero q hq hq1,map_zero]
  · intro i
    rw [← mixedFiniteCreation_intertwines_K,mixedFusionHighestAt_K,map_smul]
    simp only [mixedFusionIndexSucc,Nat.add_sub_add_right]

end AMSPhysical
#print axioms AMSPhysical.mixedFiniteCreation_highest
