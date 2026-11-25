import QuantumTypeAWeights

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

def occupationHeightZ (n L : ℕ) (x : occupationWeights (Fin (n+1)) L) : ℤ :=
  latticePairing (fun k : Fin (n+1) => (k.val:ℤ)) x.val

def occupationHeight (n L : ℕ) (x : occupationWeights (Fin (n+1)) L) : ℕ := (occupationHeightZ n L x).toNat

theorem occupationHeightZ_nonnegative (n L : ℕ) (x : occupationWeights (Fin (n+1)) L) : 0≤occupationHeightZ n L x := by
  unfold occupationHeightZ latticePairing
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (Int.natCast_nonneg k.val) (x.property.1 k)

/-- Any occupation other than the highest one admits a nonzero simple-root
raising move. -/
theorem occupation_nonhighest_donor (n L : ℕ) (x : occupationWeights (Fin (n+1)) L)
    (hx : x≠highestOccupation n L) : ∃ i : Fin n,0<x.val i.succ := by
  classical
  by_contra hn
  have hzero : ∀ i : Fin n,x.val i.succ=0 := by
    intro i
    have hnonneg := x.property.1 i.succ
    have hnot : ¬0<x.val i.succ := fun h => hn ⟨i,h⟩
    omega
  have hother : ∀ k : Fin (n+1),k≠0 → x.val k=0 := by
    intro k hk
    have hkpos : 0<k.val := by
      by_contra h
      apply hk
      apply Fin.ext
      change k.val=0
      omega
    let i : Fin n := ⟨k.val-1,by have hh := k.isLt;omega⟩
    have he : i.succ=k := by apply Fin.ext;change k.val-1+1=k.val;omega
    simpa only [he] using hzero i
  have hsum : (∑ k : Fin (n+1),x.val k)=x.val 0 := by
    apply Finset.sum_eq_single 0
    · intro k hk hk0
      exact hother k hk0
    · simp
  have hx0 : x.val 0=(L:ℤ) := by rw [x.property.2] at hsum;exact hsum.symm
  apply hx
  apply Subtype.ext
  funext k
  by_cases hk : k=0
  · subst k
    simpa [highestOccupation] using hx0
  · simp [highestOccupation,Pi.single_apply,hk,Ne.symm hk,hother k hk]

def raisedOccupation (n L : ℕ) (x : occupationWeights (Fin (n+1)) L) (i : Fin n)
    (hi : 0<x.val i.succ) : occupationWeights (Fin (n+1)) L :=
  ⟨x.val+latticeRoot i.castSucc i.succ,
    occupationWeights_move L x.val x.property i.castSucc i.succ (typeA_root_endpoints n i) (ne_of_gt hi)⟩

theorem raisedOccupation_heightZ (n L : ℕ) (x : occupationWeights (Fin (n+1)) L)
    (i : Fin n) (hi : 0<x.val i.succ) :
    occupationHeightZ n L (raisedOccupation n L x i hi)=occupationHeightZ n L x-1 := by
  unfold occupationHeightZ raisedOccupation
  rw [latticePairing_add_right,latticePairing_root_right]
  simp only [Fin.coe_castSucc,Fin.val_succ,Nat.cast_add,Nat.cast_one]
  ring

theorem raisedOccupation_height (n L : ℕ) (x : occupationWeights (Fin (n+1)) L)
    (i : Fin n) (hi : 0<x.val i.succ) :
    occupationHeight n L (raisedOccupation n L x i hi)+1=occupationHeight n L x := by
  have h₁ := occupationHeightZ_nonnegative n L x
  have h₂ := occupationHeightZ_nonnegative n L (raisedOccupation n L x i hi)
  have he := raisedOccupation_heightZ n L x i hi
  unfold occupationHeight
  omega

theorem raisedOccupation_target (n L : ℕ) (x : occupationWeights (Fin (n+1)) L)
    (i : Fin n) (hi : 0<x.val i.succ) :
    (raisedOccupation n L x i hi).val i.castSucc=x.val i.castSucc+1 := by
  change (x.val+latticeRoot i.castSucc i.succ) i.castSucc=x.val i.castSucc+1
  rw [Pi.add_apply,latticeRoot_target _ _ (typeA_root_endpoints n i)]

theorem raisedOccupation_reverse (n L : ℕ) (x : occupationWeights (Fin (n+1)) L)
    (i : Fin n) (hi : 0<x.val i.succ) :
    (raisedOccupation n L x i hi).val+latticeRoot i.succ i.castSucc=x.val := by
  change x.val+latticeRoot i.castSucc i.succ+latticeRoot i.succ i.castSucc=x.val
  rw [latticeRoot_swap]
  abel

end AMSPhysical

#print axioms AMSPhysical.occupation_nonhighest_donor
#print axioms AMSPhysical.raisedOccupation_height
