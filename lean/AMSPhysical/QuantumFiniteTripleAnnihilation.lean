import OccupationTripleBasisProperties
import QuantumTripleAnnihilationSupport

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 240000
noncomputable section
namespace AMSPhysical

def finiteTripleLeftAnnihilation (q : ℝ) (n l m c : ℕ) :
    quantumOccupationTripleSpace n (l+1) (m+1) c →ₗ[ℝ] quantumOccupationTripleSpace n l m c :=
  (occupationTripleSynthesis n l m c).comp
    ((tripleLeftAnnihilation q n).comp (occupationTripleCoefficients n (l+1) (m+1) c))

theorem occupationTripleCoefficients_leftAnnihilation (q : ℝ) (n l m c : ℕ)
    (v : quantumOccupationTripleSpace n (l+1) (m+1) c) :
    occupationTripleCoefficients n l m c (finiteTripleLeftAnnihilation q n l m c v)=
      tripleLeftAnnihilation q n (occupationTripleCoefficients n (l+1) (m+1) c v) := by
  apply occupationTripleCoefficients_synthesis
  exact tripleLeftAnnihilation_physical_support q n l m c _ (occupationTripleCoefficients_support n (l+1) (m+1) c v)

def finiteTripleRightAnnihilation (q : ℝ) (n l m c : ℕ) :
    quantumOccupationTripleSpace n l (m+1) (c+1) →ₗ[ℝ] quantumOccupationTripleSpace n l m c :=
  (occupationTripleSynthesis n l m c).comp
    ((tripleRightAnnihilation q n).comp (occupationTripleCoefficients n l (m+1) (c+1)))

theorem occupationTripleCoefficients_rightAnnihilation (q : ℝ) (n l m c : ℕ)
    (v : quantumOccupationTripleSpace n l (m+1) (c+1)) :
    occupationTripleCoefficients n l m c (finiteTripleRightAnnihilation q n l m c v)=
      tripleRightAnnihilation q n (occupationTripleCoefficients n l (m+1) (c+1) v) := by
  apply occupationTripleCoefficients_synthesis
  exact tripleRightAnnihilation_physical_support q n l m c _ (occupationTripleCoefficients_support n l (m+1) (c+1) v)

end AMSPhysical
