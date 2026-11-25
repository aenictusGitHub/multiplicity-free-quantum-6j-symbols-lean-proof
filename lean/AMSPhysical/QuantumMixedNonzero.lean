import QuantumMixedTensor
import TensorBasisDiagonal

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

/-- The constructed mixed highest-weight vector is nonzero for every rank,
every pair of symmetric degrees, and every admissible contraction index. -/
theorem mixedHighestVector_ne_zero (q : ℝ) (hq : 0<q) (n r a b : ℕ) :
    mixedHighestVector q n r a b≠0 := by
  exact tensor_basis_diagonal_ne_zero
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) (r+a))
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) (r+b))
    (shiftedOccupation n r a 0) (shiftedOccupation n r b (Fin.last n))
    (shiftedOccupation_injective n r a 0) (mixedHighestCoefficient q n r b)
    (highestOccupation n r) (mixedHighestCoefficient_ne_zero q hq n r b (highestOccupation n r))

end AMSPhysical
#print axioms AMSPhysical.mixedHighestVector_ne_zero
