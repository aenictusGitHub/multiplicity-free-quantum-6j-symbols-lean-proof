import QuantumTriplePositiveSupport
import GradedCreationPowers

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

def tripleCoordinateDegree (n : ℕ) (j : Fin 3) : OccupationTripleLattice n →+ ℤ where
  toFun p := ![(∑ i : Fin (n+1),p.1 i),(∑ i : Fin (n+1),p.2.1 i),(∑ i : Fin (n+1),p.2.2 i)] j
  map_zero' := by fin_cases j <;> simp
  map_add' p z := by
    fin_cases j <;> simp [Prod.fst_add,Prod.snd_add,Pi.add_apply,Finset.sum_add_distrib]

theorem tripleCoordinateDegree_left_shift (n : ℕ) (j : Fin 3) (i : Fin (n+1)) :
    tripleCoordinateDegree n j (tripleLeftCreationShift n i)=![1,1,0] j := by
  fin_cases j <;> simp [tripleCoordinateDegree,tripleLeftCreationShift,Pi.single_apply]

theorem tripleCoordinateDegree_right_shift (n : ℕ) (j : Fin 3) (i : Fin (n+1)) :
    tripleCoordinateDegree n j (tripleRightCreationShift n i)=![0,1,1] j := by
  fin_cases j <;> simp [tripleCoordinateDegree,tripleRightCreationShift,Pi.single_apply]

theorem tripleLeftCreation_coordinate_homogeneous (q : ℝ) (n : ℕ) (j : Fin 3) (a : ℤ)
    (f : OccupationTripleLattice n →₀ ℝ) (hf : CoefficientHomogeneous (tripleCoordinateDegree n j) a f) :
    CoefficientHomogeneous (tripleCoordinateDegree n j) (a+![1,1,0] j) (tripleLeftCreation q n f) :=
  sumWeightedTranslation_homogeneous (tripleCoordinateDegree n j) (tripleLeftCreationShift n)
    (tripleLeftCreationCoefficient q n) (![1,1,0] j) (tripleCoordinateDegree_left_shift n j) a f hf

theorem tripleRightCreation_coordinate_homogeneous (q : ℝ) (n : ℕ) (j : Fin 3) (a : ℤ)
    (f : OccupationTripleLattice n →₀ ℝ) (hf : CoefficientHomogeneous (tripleCoordinateDegree n j) a f) :
    CoefficientHomogeneous (tripleCoordinateDegree n j) (a+![0,1,1] j) (tripleRightCreation q n f) :=
  sumWeightedTranslation_homogeneous (tripleCoordinateDegree n j) (tripleRightCreationShift n)
    (tripleRightCreationCoefficient q n) (![0,1,1] j) (tripleCoordinateDegree_right_shift n j) a f hf

theorem tripleCoordinateDegree_cupBase (n : ℕ) (j : Fin 3) (l h c : ℤ) :
    tripleCoordinateDegree n j (Pi.single 0 l,Pi.single (Fin.last n) h,Pi.single 0 c)=![l,h,c] j := by
  fin_cases j <;> simp [tripleCoordinateDegree,Pi.single_apply]

end AMSPhysical
