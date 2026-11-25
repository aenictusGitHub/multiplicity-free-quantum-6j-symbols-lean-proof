import QuantumCreationSingleShift
import QuantumLatticeReflectSingle
import WeightedTranslationAlgebra

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 180000
noncomputable section
namespace AMSPhysical

abbrev OccupationTripleLattice (n : ℕ) := (Fin (n+1) → ℤ) × (Fin (n+1) → ℤ) × (Fin (n+1) → ℤ)

def tripleLeftCreationShift (n : ℕ) (i : Fin (n+1)) : OccupationTripleLattice n :=
  (Pi.single i 1,Pi.single i 1,0)

def tripleRightCreationShift (n : ℕ) (j : Fin (n+1)) : OccupationTripleLattice n :=
  (0,Pi.single j 1,Pi.single j 1)

def tripleLeftCreationCoefficient (q : ℝ) (n : ℕ) (i : Fin (n+1)) (p : OccupationTripleLattice n) : ℝ :=
  mixedCreationCoefficient q n i (p.1,p.2.1)

def tripleRightCreationCoefficient (q : ℝ) (n : ℕ) (j : Fin (n+1)) (p : OccupationTripleLattice n) : ℝ :=
  mixedCreationCoefficient q n j.rev (occupationLatticeReflect n p.2.1,occupationLatticeReflect n p.2.2)

def tripleLeftCreation (q : ℝ) (n : ℕ) : Module.End ℝ (OccupationTripleLattice n →₀ ℝ) :=
  ∑ i : Fin (n+1),weightedTranslation (tripleLeftCreationShift n i) (tripleLeftCreationCoefficient q n i)

def tripleRightCreation (q : ℝ) (n : ℕ) : Module.End ℝ (OccupationTripleLattice n →₀ ℝ) :=
  ∑ j : Fin (n+1),weightedTranslation (tripleRightCreationShift n j) (tripleRightCreationCoefficient q n j)

theorem tripleLeftCreationCoefficient_right_shift (q : ℝ) (hq : q≠0) (n : ℕ)
    (i j : Fin (n+1)) (p : OccupationTripleLattice n) :
    tripleLeftCreationCoefficient q n i (p+tripleRightCreationShift n j)=
      q^(-(if j.val ≤ i.val then 1 else 0:ℤ))*tripleLeftCreationCoefficient q n i p := by
  have h:=mixedCreationCoefficient_second_unit_shift q hq n i j (p.1,p.2.1)
  simpa only [tripleLeftCreationCoefficient,tripleRightCreationShift,Prod.fst_add,Prod.snd_add] using h

theorem tripleRightCreationCoefficient_left_shift (q : ℝ) (hq : q≠0) (n : ℕ)
    (i j : Fin (n+1)) (p : OccupationTripleLattice n) :
    tripleRightCreationCoefficient q n j (p+tripleLeftCreationShift n i)=
      q^(-(if j.val ≤ i.val then 1 else 0:ℤ))*tripleRightCreationCoefficient q n j p := by
  change mixedCreationCoefficient q n j.rev (occupationLatticeReflect n (p.2.1+Pi.single i 1),
    occupationLatticeReflect n (p.2.2+0))=_
  rw [add_zero,occupationLatticeReflect_add,occupationLatticeReflect_single]
  have he : i.rev.val ≤ j.rev.val ↔ j.val ≤ i.val := by simp only [Fin.val_rev];omega
  have h:=mixedCreationCoefficient_first_unit_shift q hq n j.rev i.rev
    (occupationLatticeReflect n p.2.1,occupationLatticeReflect n p.2.2)
  change mixedCreationCoefficient q n j.rev
    (occupationLatticeReflect n p.2.1+Pi.single i.rev 1,occupationLatticeReflect n p.2.2+0)=_ at h
  simpa only [he,add_zero,tripleRightCreationCoefficient] using h

/-- The two concrete cup creation operators commute exactly in every rank.
Their prefix and reversed-prefix crossing factors are independently matched. -/
theorem tripleCreations_commute (q : ℝ) (hq : q≠0) (n : ℕ) :
    tripleLeftCreation q n*tripleRightCreation q n=tripleRightCreation q n*tripleLeftCreation q n := by
  classical
  unfold tripleLeftCreation tripleRightCreation
  rw [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  apply sub_eq_zero.mp
  rw [weightedTranslation_commutator]
  have hc : (fun p : OccupationTripleLattice n =>
      tripleRightCreationCoefficient q n j p*tripleLeftCreationCoefficient q n i (p+tripleRightCreationShift n j)-
        tripleLeftCreationCoefficient q n i p*tripleRightCreationCoefficient q n j (p+tripleLeftCreationShift n i))=(fun _ =>0) := by
    funext p
    rw [tripleLeftCreationCoefficient_right_shift q hq,tripleRightCreationCoefficient_left_shift q hq]
    ring
  rw [hc,weightedTranslation_zero]

end AMSPhysical
#print axioms AMSPhysical.tripleCreations_commute
