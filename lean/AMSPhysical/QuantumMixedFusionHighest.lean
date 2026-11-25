import QuantumMixedNormalization
import MixedBoundaryOccupation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def shiftedOccupationWithin (n L r : ℕ) (hr : r≤L) (k : Fin (n+1))
    (t : occupationWeights (Fin (n+1)) r) : occupationWeights (Fin (n+1)) L :=
  ⟨t.val+Pi.single k ((L-r:ℕ):ℤ),by
    constructor
    · intro j
      have ht := t.property.1 j
      simp only [Pi.add_apply,Pi.single_apply]
      split_ifs <;> omega
    · simp only [Pi.add_apply,Finset.sum_add_distrib,t.property.2]
      simp only [Pi.single_apply,Finset.sum_ite_eq',Finset.mem_univ,if_true]
      omega⟩

theorem shiftedOccupationWithin_injective (n L r : ℕ) (hr : r≤L) (k : Fin (n+1)) :
    Function.Injective (shiftedOccupationWithin n L r hr k) := by
  intro x y h
  apply Subtype.ext
  have hh := congrArg Subtype.val h
  change x.val+Pi.single k ((L-r:ℕ):ℤ)=y.val+Pi.single k ((L-r:ℕ):ℤ) at hh
  exact add_right_cancel hh

theorem shiftedOccupationWithin_add (n r a : ℕ) (hr : r≤r+a) (k : Fin (n+1))
    (t : occupationWeights (Fin (n+1)) r) :
    shiftedOccupationWithin n (r+a) r hr k t=shiftedOccupation n r a k t := by
  apply Subtype.ext
  simp only [shiftedOccupationWithin,shiftedOccupation,Nat.add_sub_cancel_left]

theorem shiftedOccupationWithin_highest (n L r : ℕ) (hr : r≤L) :
    shiftedOccupationWithin n L r hr 0 (highestOccupation n r)=highestOccupation n L := by
  apply Subtype.ext
  funext k
  change (Pi.single 0 (r:ℤ)+Pi.single 0 ((L-r:ℕ):ℤ) : Fin (n+1) → ℤ) k=
    (Pi.single 0 (L:ℤ) : Fin (n+1) → ℤ) k
  simp only [Pi.add_apply,Pi.single_apply]
  split_ifs <;> omega

theorem shiftedOccupationWithin_boundary (n m r : ℕ) (hr : r≤m) :
    shiftedOccupationWithin n m r hr (Fin.last n) (highestOccupation n r)=mixedBoundaryOccupation n m r hr := rfl

/-- The existing explicitly constructed mixed highest vectors, all placed
in one fixed physical tensor product without changing its degree types. -/
def mixedFusionHighest (q : ℝ) (n l m r : ℕ) (hrl : r≤l) (hrm : r≤m) :
    quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m :=
  ∑ t : occupationWeights (Fin (n+1)) r,mixedHighestCoefficient q n r (m-r) t •
    (quantumOccupationBasis (K:=ℝ) l (shiftedOccupationWithin n l r hrl 0 t) ⊗ₜ[ℝ]
      quantumOccupationBasis (K:=ℝ) m (shiftedOccupationWithin n m r hrm (Fin.last n) t))

theorem mixedFusionHighest_add (q : ℝ) (n r a b : ℕ) (ha : r≤r+a) (hb : r≤r+b) :
    mixedFusionHighest q n (r+a) (r+b) r ha hb=mixedHighestVector q n r a b := by
  unfold mixedFusionHighest mixedHighestVector mixedOccupationTensor
  simp only [Nat.add_sub_cancel_left,shiftedOccupationWithin_add]

theorem mixedFusionHighest_E_zero (q : ℝ) (hq : 0<q) (hq1 : q≠1) (n l m r : ℕ)
    (hrl : r≤l) (hrm : r≤m) (i : Fin n) :
    typeAMixedTensor q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1)
      n l m (typeAAlgebraGenerator q n i 0) (mixedFusionHighest q n l m r hrl hrm)=0 := by
  obtain ⟨a,ha⟩ := Nat.exists_eq_add_of_le hrl
  obtain ⟨b,hb⟩ := Nat.exists_eq_add_of_le hrm
  subst l
  subst m
  rw [mixedFusionHighest_add]
  exact mixedHighestVector_E_zero q hq hq1 n r a b i

end AMSPhysical
