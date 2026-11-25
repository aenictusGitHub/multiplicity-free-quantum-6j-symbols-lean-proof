import QuantumTripleCreationShifts
import QuantumMixedAnnihilationCoefficients

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

def tripleLeftAnnihilationCoefficient (q : ℝ) (n : ℕ) (i : Fin (n+1)) (p : OccupationTripleLattice n) : ℝ :=
  mixedAnnihilationCoefficient q n i (p.1,p.2.1)

def tripleRightAnnihilationCoefficient (q : ℝ) (n : ℕ) (i : Fin (n+1)) (p : OccupationTripleLattice n) : ℝ :=
  mixedAnnihilationCoefficient q n i.rev (occupationLatticeReflect n p.2.1,occupationLatticeReflect n p.2.2)

def tripleLeftAnnihilation (q : ℝ) (n : ℕ) : Module.End ℝ (OccupationTripleLattice n →₀ ℝ) :=
  ∑ i : Fin (n+1),weightedTranslation (-tripleLeftCreationShift n i) (tripleLeftAnnihilationCoefficient q n i)

def tripleRightAnnihilation (q : ℝ) (n : ℕ) : Module.End ℝ (OccupationTripleLattice n →₀ ℝ) :=
  ∑ i : Fin (n+1),weightedTranslation (-tripleRightCreationShift n i) (tripleRightAnnihilationCoefficient q n i)

def tripleFirstContractionShift (n : ℕ) : OccupationTripleLattice n :=
  (Pi.single 0 (-1),Pi.single 0 (-1),0)

def tripleFirstContractionCoefficient (q : ℝ) (n : ℕ) (p : OccupationTripleLattice n) : ℝ :=
  qInteger q (p.1 0)*qInteger q (p.2.1 0)

def tripleFirstContraction (q : ℝ) (n : ℕ) : Module.End ℝ (OccupationTripleLattice n →₀ ℝ) :=
  weightedTranslation (tripleFirstContractionShift n) (tripleFirstContractionCoefficient q n)

def tripleTransferShift (n : ℕ) : OccupationTripleLattice n :=
  (Pi.single 0 (-1),0,Pi.single 0 1)

def tripleTransferCoefficient (q : ℝ) (n : ℕ) (p : OccupationTripleLattice n) : ℝ :=
  qInteger q (p.1 0)*(-1:ℝ)^n*
    q^(-(n:ℤ)-(∑ i : Fin (n+1),p.2.1 i)-(∑ i : Fin (n+1),p.2.2 i)-p.2.1 0)

def tripleTransfer (q : ℝ) (n : ℕ) : Module.End ℝ (OccupationTripleLattice n →₀ ℝ) :=
  weightedTranslation (tripleTransferShift n) (tripleTransferCoefficient q n)

end AMSPhysical
