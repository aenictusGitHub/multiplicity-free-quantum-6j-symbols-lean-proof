import QuantumTriplePairInsertion

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

theorem occupationLatticeReflect_involution (n : ℕ) (x : Fin (n+1) → ℤ) :
    occupationLatticeReflect n (occupationLatticeReflect n x)=x := by
  funext i
  simp only [occupationLatticeReflect,Fin.rev_rev]

theorem occupationLatticeReflect_neg (n : ℕ) (x : Fin (n+1) → ℤ) :
    occupationLatticeReflect n (-x)= -occupationLatticeReflect n x := rfl

def tripleReversePairInsertion (n : ℕ) (x : Fin (n+1) → ℤ) : OccupationPairLattice n → OccupationTripleLattice n :=
  fun p =>(x,occupationLatticeReflect n p.1,occupationLatticeReflect n p.2)

def tripleReversePairInsert (n : ℕ) (x : Fin (n+1) → ℤ) :
    (OccupationPairLattice n →₀ ℝ) →ₗ[ℝ] (OccupationTripleLattice n →₀ ℝ) :=
  Finsupp.lmapDomain ℝ ℝ (tripleReversePairInsertion n x)

theorem tripleReversePairInsert_single (n : ℕ) (x y z : Fin (n+1) → ℤ) (a : ℝ) :
    tripleReversePairInsert n x (Finsupp.single (y,z) a)=
      Finsupp.single (x,occupationLatticeReflect n y,occupationLatticeReflect n z) a := Finsupp.mapDomain_single

theorem tripleReversePairInsert_creation (q : ℝ) (n : ℕ) (x : Fin (n+1) → ℤ)
    (f : OccupationPairLattice n →₀ ℝ) :
    tripleReversePairInsert n x (pairLatticeCreation q n f)=tripleRightCreation q n (tripleReversePairInsert n x f) := by
  unfold pairLatticeCreation tripleRightCreation
  simp only [LinearMap.sum_apply,map_sum]
  calc
    _ = ∑ i : Fin (n+1),weightedTranslation (tripleRightCreationShift n i.rev)
        (tripleRightCreationCoefficient q n i.rev) (tripleReversePairInsert n x f) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply weightedTranslation_naturality (tripleReversePairInsertion n x)
        (mixedCreationShift n i) (tripleRightCreationShift n i.rev)
        (mixedCreationCoefficient q n i) (tripleRightCreationCoefficient q n i.rev)
      · intro p
        ext j <;> simp [tripleReversePairInsertion,mixedCreationShift,tripleRightCreationShift,
          occupationLatticeReflect_add,occupationLatticeReflect_single]
      · intro p
        simp only [tripleReversePairInsertion,tripleRightCreationCoefficient,Fin.rev_rev,occupationLatticeReflect_involution]
    _ = _ := Equiv.sum_comp Fin.revPerm (fun i : Fin (n+1) =>
      weightedTranslation (tripleRightCreationShift n i) (tripleRightCreationCoefficient q n i) (tripleReversePairInsert n x f))

theorem tripleReversePairInsert_annihilation (q : ℝ) (n : ℕ) (x : Fin (n+1) → ℤ)
    (f : OccupationPairLattice n →₀ ℝ) :
    tripleReversePairInsert n x (pairLatticeAnnihilation q n f)=tripleRightAnnihilation q n (tripleReversePairInsert n x f) := by
  unfold pairLatticeAnnihilation tripleRightAnnihilation
  simp only [LinearMap.sum_apply,map_sum]
  calc
    _ = ∑ i : Fin (n+1),weightedTranslation (-tripleRightCreationShift n i.rev)
        (tripleRightAnnihilationCoefficient q n i.rev) (tripleReversePairInsert n x f) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply weightedTranslation_naturality (tripleReversePairInsertion n x)
        (-mixedCreationShift n i) (-tripleRightCreationShift n i.rev)
        (mixedAnnihilationCoefficient q n i) (tripleRightAnnihilationCoefficient q n i.rev)
      · intro p
        ext j <;> simp [tripleReversePairInsertion,mixedCreationShift,tripleRightCreationShift,
          occupationLatticeReflect_add,occupationLatticeReflect_neg,occupationLatticeReflect_single]
      · intro p
        simp only [tripleReversePairInsertion,tripleRightAnnihilationCoefficient,Fin.rev_rev,occupationLatticeReflect_involution]
    _ = _ := Equiv.sum_comp Fin.revPerm (fun i : Fin (n+1) =>
      weightedTranslation (-tripleRightCreationShift n i) (tripleRightAnnihilationCoefficient q n i) (tripleReversePairInsert n x f))

end AMSPhysical
