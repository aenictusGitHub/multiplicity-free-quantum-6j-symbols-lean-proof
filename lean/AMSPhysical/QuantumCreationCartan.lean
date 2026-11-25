import QuantumCreationLowering

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical

def pairLatticeCartanWeight (n : ℕ) (i : Fin n) (p : OccupationPairLattice n) : ℤ :=
  simpleOccupationWeight n p.1 i-simpleOccupationWeight n p.2 i

def pairLatticeCartan (q : ℝ) (n : ℕ) (i : Fin n) (s : ℤ) : Module.End ℝ (OccupationPairLattice n →₀ ℝ) :=
  weightedTranslation 0 (fun p =>q^(s*pairLatticeCartanWeight n i p))

theorem pairLatticeCartanWeight_creation (n : ℕ) (i : Fin n) (k : Fin (n+1)) (p : OccupationPairLattice n) :
    pairLatticeCartanWeight n i (p+mixedCreationShift n k)=pairLatticeCartanWeight n i p := by
  unfold pairLatticeCartanWeight mixedCreationShift
  change simpleOccupationWeight n (p.1+Pi.single k 1) i-simpleOccupationWeight n (p.2+Pi.single k 1) i=_
  rw [simpleOccupationWeight_add_single,simpleOccupationWeight_add_single]
  ring

theorem pairLatticeCreation_commutes_cartan (q : ℝ) (n : ℕ) (i : Fin n) (s : ℤ) :
    pairLatticeCreation q n*pairLatticeCartan q n i s=
      pairLatticeCartan q n i s*pairLatticeCreation q n := by
  unfold pairLatticeCreation
  rw [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  unfold pairLatticeCartan
  apply sub_eq_zero.mp
  rw [weightedTranslation_commutator]
  simp only [add_zero,pairLatticeCartanWeight_creation]
  have hz : (fun p : OccupationPairLattice n =>q^(s*pairLatticeCartanWeight n i p)*mixedCreationCoefficient q n k p-
      mixedCreationCoefficient q n k p*q^(s*pairLatticeCartanWeight n i p))=(fun _ =>0) := by funext p;ring
  rw [hz,weightedTranslation_zero]

end AMSPhysical
#print axioms AMSPhysical.pairLatticeCreation_commutes_cartan
