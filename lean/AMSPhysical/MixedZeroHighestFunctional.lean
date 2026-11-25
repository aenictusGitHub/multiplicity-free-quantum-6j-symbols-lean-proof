import GlobalTypeILeftVertices
import PhysicalAllFirstFunctional
import FiniteWeightedDuality
import CompactHighestProjectionOrthogonal
import CompactHighestOnChannel

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def mixedZeroHighestFunctional (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (p s : ℕ) :=
  (globalMixedPairRealization q hq hq1 n hn p s 0).onChannel.pairing
    (globalMixedPairRealization q hq hq1 n hn p s 0).onChannel.highest

theorem mixedZeroHighestFunctional_projection (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (p s : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) p ⊗[ℝ]
      quantumOccupationSpace ℝ (Fin (n+1)) s) :
    mixedZeroHighestFunctional q hq hq1 n hn p s
      ((globalMixedPairRealization q hq hq1 n hn p s 0).channelProjection v) =
      occupationTensorCoefficients n p s v ((highestOccupation n p).val,(lowestOccupation n s).val) := by
  change (globalMixedPairRealization q hq hq1 n hn p s 0).channelPair
    ⟨(globalMixedPairRealization q hq hq1 n hn p s 0).highest,algebraCyclicSpan_self _ _⟩
    ((globalMixedPairRealization q hq hq1 n hn p s 0).channelProjection v) = _
  rw [← CompactHighestRealization.channelProjection_adjoint]
  change mixedTensorBilin q n p s (globalMixedPairRealization q hq hq1 n hn p s 0).highest v = _
  rw [globalMixedPairRealization_zero_highest,mixedTensorBilin_symm]
  rw [← Module.Basis.tensorProduct_apply' (quantumOccupationBasis (K:=ℝ) p)
    (quantumOccupationBasis (K:=ℝ) s) (highestOccupation n p,lowestOccupation n s)]
  change finiteWeightedPair
    (fun xy : occupationWeights (Fin (n+1)) p × occupationWeights (Fin (n+1)) s=>
      occupationCompactWeight q n p xy.1*occupationOppositeWeight q n s xy.2)
    ((quantumOccupationBasis (K:=ℝ) p).tensorProduct (quantumOccupationBasis (K:=ℝ) s)).equivFun.toLinearMap
    v (((quantumOccupationBasis (K:=ℝ) p).tensorProduct (quantumOccupationBasis (K:=ℝ) s))
      (highestOccupation n p,lowestOccupation n s)) = _
  rw [finiteWeightedPair_basis_right]
  simp only [occupationCompactWeight_highest q hq,occupationOppositeWeight_highest q hq,
    one_mul,Module.Basis.equivFun_apply]
  exact (occupationTensorCoefficients_repr n p s v _ _).symm

end AMSPhysical
#print axioms AMSPhysical.mixedZeroHighestFunctional_projection
