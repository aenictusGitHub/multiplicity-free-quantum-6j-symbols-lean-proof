import OccupationTensorSynthesis
import QuantumOccupationAnnihilationSupport

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 180000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- The independently specified raw occupation annihilation, restricted to
the actual finite physical degrees through a proved inverse coefficient map. -/
def mixedFiniteRawAnnihilation (q : ℝ) (n l m : ℕ) :
    (quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1)) →ₗ[ℝ]
      (quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :=
  (occupationTensorSynthesis n l m).comp
    ((pairLatticeAnnihilation q n).comp (occupationTensorCoefficients n (l+1) (m+1)))

theorem occupationTensorCoefficients_annihilation (q : ℝ) (n l m : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) (l+1) ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) (m+1)) :
    occupationTensorCoefficients n l m (mixedFiniteRawAnnihilation q n l m v)=
      pairLatticeAnnihilation q n (occupationTensorCoefficients n (l+1) (m+1) v) := by
  apply occupationTensorCoefficients_synthesis
  exact pairLatticeAnnihilation_physical_support q n l m _
    (occupationTensorCoefficients_support n (l+1) (m+1) v)

end AMSPhysical
