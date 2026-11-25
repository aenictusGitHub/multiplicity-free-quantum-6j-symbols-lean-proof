import QuantumSymmetricTensor

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

theorem pairSymmetricRaising_zero_coordinate (q : ℝ) (n : ℕ) (i : Fin n)
    (f : OccupationPairLattice n →₀ ℝ) (hf : pairSymmetricRaising q n i f=0)
    (x y : Fin (n+1) → ℤ) :
    f (x-latticeRoot i.castSucc i.succ,y)*qInteger q (x i.succ+1)*q^(simpleOccupationWeight n y i)+
      f (x,y-latticeRoot i.castSucc i.succ)*qInteger q (y i.succ+1)=0 := by
  rw [← pairSymmetricRaising_coordinate,hf,Finsupp.zero_apply]

end AMSPhysical
