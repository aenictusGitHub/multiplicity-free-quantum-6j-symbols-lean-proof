import QuantumTripleAnnihilation
import WeightedTranslationNaturality

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

def triplePairInsertion (n : ℕ) (z : Fin (n+1) → ℤ) : OccupationPairLattice n → OccupationTripleLattice n :=
  fun p =>(p.1,p.2,z)

def triplePairInsert (n : ℕ) (z : Fin (n+1) → ℤ) :
    (OccupationPairLattice n →₀ ℝ) →ₗ[ℝ] (OccupationTripleLattice n →₀ ℝ) :=
  Finsupp.lmapDomain ℝ ℝ (triplePairInsertion n z)

theorem triplePairInsert_single (n : ℕ) (z : Fin (n+1) → ℤ) (x y : Fin (n+1) → ℤ) (a : ℝ) :
    triplePairInsert n z (Finsupp.single (x,y) a)=Finsupp.single (x,y,z) a := Finsupp.mapDomain_single

theorem triplePairInsert_creation (q : ℝ) (n : ℕ) (z : Fin (n+1) → ℤ)
    (f : OccupationPairLattice n →₀ ℝ) :
    triplePairInsert n z (pairLatticeCreation q n f)=tripleLeftCreation q n (triplePairInsert n z f) := by
  unfold pairLatticeCreation tripleLeftCreation
  simp only [LinearMap.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply weightedTranslation_naturality (triplePairInsertion n z)
    (mixedCreationShift n i) (tripleLeftCreationShift n i)
    (mixedCreationCoefficient q n i) (tripleLeftCreationCoefficient q n i)
  · intro p
    ext j <;> simp [triplePairInsertion,mixedCreationShift,tripleLeftCreationShift]
  · intro p
    rfl

theorem triplePairInsert_annihilation (q : ℝ) (n : ℕ) (z : Fin (n+1) → ℤ)
    (f : OccupationPairLattice n →₀ ℝ) :
    triplePairInsert n z (pairLatticeAnnihilation q n f)=tripleLeftAnnihilation q n (triplePairInsert n z f) := by
  unfold pairLatticeAnnihilation tripleLeftAnnihilation
  simp only [LinearMap.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply weightedTranslation_naturality (triplePairInsertion n z)
    (-mixedCreationShift n i) (-tripleLeftCreationShift n i)
    (mixedAnnihilationCoefficient q n i) (tripleLeftAnnihilationCoefficient q n i)
  · intro p
    ext j <;> simp [triplePairInsertion,mixedCreationShift,tripleLeftCreationShift]
  · intro p
    rfl

end AMSPhysical
