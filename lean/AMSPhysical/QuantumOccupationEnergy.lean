import QuantumOccupationGraph

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def occupationSquareSum (x : ι → ℤ) : ℤ := ∑ k,(x k)^2

theorem latticeRoot_square_sum (a b : ι) (hab : a≠b) : occupationSquareSum (latticeRoot a b)=2 := by
  classical
  have h : ∀ k,(latticeRoot a b k)^2=(Pi.single a (1:ℤ) : ι → ℤ) k+(Pi.single b (1:ℤ) : ι → ℤ) k := by
    intro k
    by_cases hka : k=a
    · subst k
      simp [latticeRoot,Pi.single_apply,hab,Ne.symm hab]
    · by_cases hkb : k=b
      · subst k
        simp [latticeRoot,Pi.single_apply,hab,Ne.symm hab]
      · simp [latticeRoot,Pi.single_apply,hka,Ne.symm hka,hkb,Ne.symm hkb]
  simp [occupationSquareSum,h,Finset.sum_add_distrib,Pi.single_apply,eq_comm]

theorem occupationSquareSum_root (x : ι → ℤ) (a b : ι) (hab : a≠b) :
    occupationSquareSum (x+latticeRoot a b)=occupationSquareSum x+2*(x a-x b)+2 := by
  calc
    _ = occupationSquareSum x+2*latticePairing x (latticeRoot a b)+occupationSquareSum (latticeRoot a b) := by
      unfold occupationSquareSum latticePairing
      rw [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Pi.add_apply]
      ring
    _ = _ := by rw [latticePairing_root_right,latticeRoot_square_sum a b hab]

/-- Half the square-sum difference is integral for fixed total occupation.
This exponent agrees with the usual factorial compact metric. -/
def occupationEnergy (n L : ℕ) (x : occupationWeights (Fin (n+1)) L) : ℤ :=
  (occupationSquareSum x.val-(L:ℤ)^2)/2

theorem raisedOccupation_energy (n L : ℕ) (x : occupationWeights (Fin (n+1)) L)
    (i : Fin n) (hi : 0<x.val i.succ) :
    occupationEnergy n L (raisedOccupation n L x i hi)=
      occupationEnergy n L x+x.val i.castSucc-x.val i.succ+1 := by
  have he := occupationSquareSum_root x.val i.castSucc i.succ (typeA_root_endpoints n i)
  change occupationSquareSum (raisedOccupation n L x i hi).val=
    occupationSquareSum x.val+2*(x.val i.castSucc-x.val i.succ)+2 at he
  unfold occupationEnergy
  omega

theorem raisedOccupation_source (n L : ℕ) (x : occupationWeights (Fin (n+1)) L)
    (i : Fin n) (hi : 0<x.val i.succ) :
    (raisedOccupation n L x i hi).val i.succ=x.val i.succ-1 := by
  change (x.val+latticeRoot i.castSucc i.succ) i.succ=x.val i.succ-1
  rw [Pi.add_apply,latticeRoot_source _ _ (typeA_root_endpoints n i)]
  ring

theorem raisedOccupation_other (n L : ℕ) (x : occupationWeights (Fin (n+1)) L)
    (i : Fin n) (hi : 0<x.val i.succ) (k : Fin (n+1)) (hka : k≠i.castSucc) (hkb : k≠i.succ) :
    (raisedOccupation n L x i hi).val k=x.val k := by
  change (x.val+latticeRoot i.castSucc i.succ) k=x.val k
  simp [latticeRoot,Pi.single_apply,hka,Ne.symm hka,hkb,Ne.symm hkb]

end AMSPhysical
#print axioms AMSPhysical.raisedOccupation_energy
