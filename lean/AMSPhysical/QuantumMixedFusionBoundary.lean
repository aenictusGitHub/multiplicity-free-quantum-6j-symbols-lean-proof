import QuantumMixedFusionHighest
import OccupationTensorCoefficients
import TensorBasisSlices

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

/-- The constructed physical highest vectors have a literal Kronecker
boundary: their free leading coefficients are exactly the channel labels. -/
theorem mixedFusionHighest_boundary_coefficient (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n) (l m r : ℕ)
    (hrl : r≤l) (hrm : r≤m) (y : occupationWeights (Fin (n+1)) m) :
    occupationTensorCoefficients n l m (mixedFusionHighest q n l m r hrl hrm)
      ((highestOccupation n l).val,y.val)=(if mixedBoundaryOccupation n m r hrm=y then 1 else 0) := by
  classical
  rw [occupationTensorCoefficients_repr]
  have h := tensor_sum_left_coefficient
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l)
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)
    (shiftedOccupationWithin n l r hrl 0) (shiftedOccupationWithin_injective n l r hrl 0)
    (mixedHighestCoefficient q n r (m-r))
    (fun t => quantumOccupationBasis (K:=ℝ) m (shiftedOccupationWithin n m r hrm (Fin.last n) t))
    (highestOccupation n r) y
  rw [shiftedOccupationWithin_highest,mixedHighestCoefficient_highest q hq n r (m-r) hn,
    shiftedOccupationWithin_boundary,Module.Basis.repr_self,one_mul] at h
  simp only [← TensorProduct.smul_tmul',Finsupp.single_apply] at h
  exact h

end AMSPhysical
