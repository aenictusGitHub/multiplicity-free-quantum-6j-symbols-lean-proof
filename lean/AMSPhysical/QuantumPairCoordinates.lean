import QuantumPairRaising

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

theorem pairLatticeRaising_coordinate (q : ℝ) (n : ℕ) (i : Fin n)
    (f : OccupationPairLattice n →₀ ℝ) (x y : Fin (n+1) → ℤ) :
    pairLatticeRaising q n i f (x,y)=
      f (x-latticeRoot i.castSucc i.succ,y)*qInteger q (x i.succ+1)*q^(-simpleOccupationWeight n y i)+
      f (x,y+latticeRoot i.castSucc i.succ)*qInteger q (y i.castSucc+1) := by
  simp only [pairLatticeRaising,LinearMap.add_apply,Finsupp.add_apply,weightedTranslation_apply]
  have hs : (x,y)-(latticeRoot i.castSucc i.succ,0)=(x-latticeRoot i.castSucc i.succ,y) := by ext <;> simp
  have ht : (x,y)-(0,-latticeRoot i.castSucc i.succ)=(x,y+latticeRoot i.castSucc i.succ) := by ext <;> simp
  rw [hs,ht]
  have hj : (x-latticeRoot i.castSucc i.succ) i.succ=x i.succ+1 := by
    rw [Pi.sub_apply,latticeRoot_source _ _ (typeA_root_endpoints n i)]
    ring
  have hi : (y+latticeRoot i.castSucc i.succ) i.castSucc=y i.castSucc+1 := by
    rw [Pi.add_apply,latticeRoot_target _ _ (typeA_root_endpoints n i)]
  simp only [hj,hi,mul_assoc]

end AMSPhysical
