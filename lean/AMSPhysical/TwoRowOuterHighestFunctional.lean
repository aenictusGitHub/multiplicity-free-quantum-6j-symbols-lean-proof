import ActualTwoRowVertexEntry
import QuantumSymmetricDualAdjoint
import FiniteBendingMetric

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem globalTwoRowOut_highest_functional (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (S r : ℕ) (hr : 2*r≤S)
    (d c : ℕ) (hS : d+c=S) (hd : r≤d) (hc : r≤c)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) d ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) c) :
    (actualTwoRowCarrier q hq hq1 n hn S r hr).frame.pairing
      (actualTwoRowCarrier q hq hq1 n hn S r hr).frame.highest
      (globalTwoRowOut q hq hq1 n hn S r hr d c hS hd hc v) =
      symmetricTensorBilin q n d c (normalizedTwoRowHighest q n hn d c r hd hc) v := by
  let X:=twoRowHighestRealization q hq hq1 n hn S r d c hS hd hc
  let Y:=globalTwoRowCarrier q hq hq1 n hn S r hr
  have he:=X.transport_highest_functional (ne_of_gt hq) Y (X.channelProjection v)
  have hp:=X.channelProjection_adjoint ⟨X.highest,algebraCyclicSpan_self _ _⟩ v
  exact he.trans hp.symm

theorem twoRowHighest_metric_boundary (q : ℝ) (hq : 0<q) (n : ℕ) (hn : 0<n)
    (d c r : ℕ) (hd : r≤d) (hc : r≤c) (x : occupationWeights (Fin (n+1)) c) :
    symmetricTensorBilin q n d c (normalizedTwoRowHighest q n hn d c r hd hc)
      (quantumOccupationBasis (K:=ℝ) d (highestOccupation n d) ⊗ₜ[ℝ] quantumOccupationBasis (K:=ℝ) c x) =
      occupationCompactWeight q n c x * (Real.sqrt (couplingNormClosed q (d-r) (c-r) r))⁻¹ *
        (if twoVertexOccupation n hn c ⟨r,by omega⟩=x then 1 else 0) := by
  rw [← Module.Basis.tensorProduct_apply' (quantumOccupationBasis (K:=ℝ) d)
    (quantumOccupationBasis (K:=ℝ) c) (highestOccupation n d,x)]
  change finiteWeightedPair
    (fun xy : occupationWeights (Fin (n+1)) d × occupationWeights (Fin (n+1)) c=>
      occupationCompactWeight q n d xy.1*occupationCompactWeight q n c xy.2)
    ((quantumOccupationBasis (K:=ℝ) d).tensorProduct (quantumOccupationBasis (K:=ℝ) c)).equivFun.toLinearMap
    _ (((quantumOccupationBasis (K:=ℝ) d).tensorProduct (quantumOccupationBasis (K:=ℝ) c))
      (highestOccupation n d,x)) = _
  rw [finiteWeightedPair_basis_right,occupationCompactWeight_highest q hq,one_mul]
  simp only [Module.Basis.equivFun_apply]
  rw [← occupationTensorCoefficients_repr,normalizedTwoRowHighest,map_smul,Finsupp.smul_apply,
    twoRowHighest_boundary_coefficient]
  change _ * (_ * _)=_
  ring

end AMSPhysical
#print axioms AMSPhysical.globalTwoRowOut_highest_functional
#print axioms AMSPhysical.twoRowHighest_metric_boundary
