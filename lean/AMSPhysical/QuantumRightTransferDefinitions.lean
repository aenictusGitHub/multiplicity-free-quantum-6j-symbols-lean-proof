import QuantumTripleAnnihilation
import QuantumCreationBoundary

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

def tripleLastContractionShift (n : ℕ) : OccupationTripleLattice n :=
  (0,Pi.single 0 (-1),Pi.single 0 (-1))

def tripleLastContractionPrefactor (q : ℝ) (n : ℕ) (p : OccupationTripleLattice n) : ℝ :=
  (-1:ℝ)^n*q^(-(n:ℤ)-(∑ i : Fin (n+1),p.2.1 i)-(∑ i : Fin (n+1),p.2.2 i)+p.2.1 0+p.2.2 0)

def tripleLastContractionCoefficient (q : ℝ) (n : ℕ) (p : OccupationTripleLattice n) : ℝ :=
  tripleLastContractionPrefactor q n p*qInteger q (p.2.1 0)*qInteger q (p.2.2 0)

def tripleLastContraction (q : ℝ) (n : ℕ) : Module.End ℝ (OccupationTripleLattice n →₀ ℝ) :=
  weightedTranslation (tripleLastContractionShift n) (tripleLastContractionCoefficient q n)

def tripleReverseTransferShift (n : ℕ) : OccupationTripleLattice n :=
  (Pi.single 0 1,0,Pi.single 0 (-1))

def tripleReverseTransferCoefficient (q : ℝ) (n : ℕ) (p : OccupationTripleLattice n) : ℝ :=
  tripleLastContractionPrefactor q n p*q^(-p.1 0)*qInteger q (p.2.2 0)

def tripleReverseTransfer (q : ℝ) (n : ℕ) : Module.End ℝ (OccupationTripleLattice n →₀ ℝ) :=
  weightedTranslation (tripleReverseTransferShift n) (tripleReverseTransferCoefficient q n)

theorem occupationStrictPrefix_reflect_last (n : ℕ) (x : Fin (n+1) → ℤ) :
    occupationStrictPrefix n (Fin.last n) (occupationLatticeReflect n x)=
      (∑ i : Fin (n+1),x i)-x 0 := by
  have h:=occupationPrefix_strict n (Fin.last n) (occupationLatticeReflect n x)
  rw [occupationPrefix_last_sum,occupationLatticeReflect_sum] at h
  change (∑ i : Fin (n+1),x i)=occupationStrictPrefix n (Fin.last n) (occupationLatticeReflect n x)+x (Fin.last n).rev at h
  rw [Fin.rev_last] at h
  omega

theorem tripleRightAnnihilationCoefficient_zero (q : ℝ) (n : ℕ) (p : OccupationTripleLattice n) :
    tripleRightAnnihilationCoefficient q n 0 p=tripleLastContractionCoefficient q n p := by
  unfold tripleRightAnnihilationCoefficient mixedAnnihilationCoefficient
  rw [Fin.rev_zero]
  simp only [Fin.val_last,occupationStrictPrefix_reflect_last,occupationLatticeReflect,Fin.rev_last]
  unfold tripleLastContractionCoefficient tripleLastContractionPrefactor
  have he : -(n:ℤ)-((∑ i : Fin (n+1),p.2.1 i)-p.2.1 0)-((∑ i : Fin (n+1),p.2.2 i)-p.2.2 0)=
      -(n:ℤ)-(∑ i : Fin (n+1),p.2.1 i)-(∑ i : Fin (n+1),p.2.2 i)+p.2.1 0+p.2.2 0 := by ring
  rw [he]

theorem tripleLeftCreationCoefficient_zero (q : ℝ) (n : ℕ) (p : OccupationTripleLattice n) :
    tripleLeftCreationCoefficient q n 0 p=q^(-p.1 0-p.2.1 0) := by
  simp only [tripleLeftCreationCoefficient,mixedCreationCoefficient,occupationPrefix_zero,
    Fin.val_zero,Nat.cast_zero,pow_zero,one_mul,neg_zero,zero_sub]

end AMSPhysical
