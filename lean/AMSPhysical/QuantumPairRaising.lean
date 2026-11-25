import WeightedTranslation
import QuantumTypeAWeights

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
namespace AMSPhysical

abbrev OccupationPairLattice (n : ℕ) := (Fin (n+1) → ℤ) × (Fin (n+1) → ℤ)

def pairLatticeRaising (q : ℝ) (n : ℕ) (i : Fin n) :
    Module.End ℝ (OccupationPairLattice n →₀ ℝ) :=
  weightedTranslation (latticeRoot i.castSucc i.succ,0)
    (fun p => qInteger q (p.1 i.succ)*q^(-simpleOccupationWeight n p.2 i))+
  weightedTranslation (0,-latticeRoot i.castSucc i.succ)
    (fun p => qInteger q (p.2 i.castSucc))

theorem pairLatticeRaising_single (q : ℝ) (n : ℕ) (i : Fin n)
    (x y : Fin (n+1) → ℤ) :
    pairLatticeRaising q n i (Finsupp.single (x,y) 1)=
      Finsupp.single (x+latticeRoot i.castSucc i.succ,y)
        (qInteger q (x i.succ)*q^(-simpleOccupationWeight n y i))+
      Finsupp.single (x,y-latticeRoot i.castSucc i.succ) (qInteger q (y i.castSucc)) := by
  simp [pairLatticeRaising,sub_eq_add_neg]

/-- The exact coefficient recurrence on the unrestricted pair lattice.
Zero coefficients outside the actual nonnegative occupations retain every
physical boundary, rather than discarding boundary equations. -/
theorem pairLatticeRaising_zero_coordinate (q : ℝ) (n : ℕ) (i : Fin n)
    (f : OccupationPairLattice n →₀ ℝ) (hf : pairLatticeRaising q n i f=0)
    (x y : Fin (n+1) → ℤ) :
    f (x-latticeRoot i.castSucc i.succ,y)*qInteger q (x i.succ+1)*q^(-simpleOccupationWeight n y i)+
      f (x,y+latticeRoot i.castSucc i.succ)*qInteger q (y i.castSucc+1)=0 := by
  have h := congrArg (fun g : OccupationPairLattice n →₀ ℝ => g (x,y)) hf
  dsimp only at h
  simp only [pairLatticeRaising,LinearMap.add_apply,Finsupp.add_apply,
    weightedTranslation_apply,Finsupp.zero_apply] at h
  have hs : (x,y)-(latticeRoot i.castSucc i.succ,0)=(x-latticeRoot i.castSucc i.succ,y) := by ext <;> simp
  have ht : (x,y)-(0,-latticeRoot i.castSucc i.succ)=(x,y+latticeRoot i.castSucc i.succ) := by ext <;> simp
  rw [hs,ht] at h
  have hj : (x-latticeRoot i.castSucc i.succ) i.succ=x i.succ+1 := by
    rw [Pi.sub_apply,latticeRoot_source _ _ (typeA_root_endpoints n i)]
    ring
  have hi : (y+latticeRoot i.castSucc i.succ) i.castSucc=y i.castSucc+1 := by
    rw [Pi.add_apply,latticeRoot_target _ _ (typeA_root_endpoints n i)]
  simpa only [hj,hi,mul_assoc] using h

end AMSPhysical
