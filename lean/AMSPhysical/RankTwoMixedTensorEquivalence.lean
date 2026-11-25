import RankTwoOppositeEquivalence
import QuantumRankTwoTensor
import QuantumMixedTensor
import QuantumReverseMixedTensor
import QuantumTensorMetric
import TensorWeightedIsometries

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def rankTwoMixedPairEquiv (l m : ℕ) :
    finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m ≃ₗ[ℝ]
      quantumOccupationSpace ℝ (Fin 2) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin 2) m :=
  TensorProduct.congr (rankTwoSymmetricEquiv l) (rankTwoOppositeEquiv m)

def rankTwoReverseMixedPairEquiv (l m : ℕ) :
    finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m ≃ₗ[ℝ]
      quantumOccupationSpace ℝ (Fin 2) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin 2) m :=
  TensorProduct.congr (rankTwoOppositeEquiv l) (rankTwoSymmetricEquiv m)

theorem rankTwoMixedPairEquiv_intertwines (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (l m : ℕ) (z : UqTypeA q 1) (v : finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) :
    rankTwoMixedPairEquiv l m (finiteTensorRepresentation q hq hD l m (rankTwoToSL2 q z) v)=
      typeAMixedTensor q hq hD 1 l m z (rankTwoMixedPairEquiv l m v) := by
  change TensorProduct.map (rankTwoSymmetricEquiv l).toLinearMap (rankTwoOppositeEquiv m).toLinearMap
    (((tensorRepresentation q hq (finiteQuantumRepresentation q hq hD l) (finiteQuantumRepresentation q hq hD m)).comp
      (rankTwoToSL2 q)) z v)=_
  rw [← rankTwo_tensor_pullback]
  exact typeA_intertwiner_tensor q hq 1 _ _ _ _ _ _
    (rankTwoSymmetricEquiv_intertwines q hq hD l) (rankTwoOppositeEquiv_intertwines q hq hD m) z v

theorem rankTwoReverseMixedPairEquiv_intertwines (q : ℝ) (hq : q≠0) (hD : q-q⁻¹≠0)
    (l m : ℕ) (z : UqTypeA q 1) (v : finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) :
    rankTwoReverseMixedPairEquiv l m (finiteTensorRepresentation q hq hD l m (rankTwoToSL2 q z) v)=
      typeAReverseMixedTensor q hq hD 1 l m z (rankTwoReverseMixedPairEquiv l m v) := by
  change TensorProduct.map (rankTwoOppositeEquiv l).toLinearMap (rankTwoSymmetricEquiv m).toLinearMap
    (((tensorRepresentation q hq (finiteQuantumRepresentation q hq hD l) (finiteQuantumRepresentation q hq hD m)).comp
      (rankTwoToSL2 q)) z v)=_
  rw [← rankTwo_tensor_pullback]
  exact typeA_intertwiner_tensor q hq 1 _ _ _ _ _ _
    (rankTwoOppositeEquiv_intertwines q hq hD l) (rankTwoSymmetricEquiv_intertwines q hq hD m) z v

theorem rankTwoMixedPairEquiv_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (v w : finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) :
    mixedTensorBilin q 1 l m (rankTwoMixedPairEquiv l m v) (rankTwoMixedPairEquiv l m w)=quantumTensorBilin q l m v w := by
  exact tensorWeightedBilin_map_isometry
    (standardWeightBasis (K:=ℝ) l) (standardWeightBasis (K:=ℝ) m)
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin 2) l) (quantumOccupationBasis (K:=ℝ) (ι:=Fin 2) m)
    (fun k =>quantumWeight q l k.val) (fun k =>quantumWeight q m k.val)
    (occupationCompactWeight q 1 l) (occupationOppositeWeight q 1 m)
    (rankTwoSymmetricEquiv l).toLinearMap (rankTwoOppositeEquiv m).toLinearMap
    (rankTwoSymmetricEquiv_isometry q hq hq1 l) (rankTwoOppositeEquiv_isometry q hq hq1 m) v w

theorem rankTwoReverseMixedPairEquiv_isometry (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ)
    (v w : finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) :
    reverseMixedTensorBilin q 1 l m (rankTwoReverseMixedPairEquiv l m v) (rankTwoReverseMixedPairEquiv l m w)=
      quantumTensorBilin q l m v w := by
  exact tensorWeightedBilin_map_isometry
    (standardWeightBasis (K:=ℝ) l) (standardWeightBasis (K:=ℝ) m)
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin 2) l) (quantumOccupationBasis (K:=ℝ) (ι:=Fin 2) m)
    (fun k =>quantumWeight q l k.val) (fun k =>quantumWeight q m k.val)
    (occupationOppositeWeight q 1 l) (occupationCompactWeight q 1 m)
    (rankTwoOppositeEquiv l).toLinearMap (rankTwoSymmetricEquiv m).toLinearMap
    (rankTwoOppositeEquiv_isometry q hq hq1 l) (rankTwoSymmetricEquiv_isometry q hq hq1 m) v w

end AMSPhysical
#print axioms AMSPhysical.rankTwoMixedPairEquiv_intertwines
#print axioms AMSPhysical.rankTwoReverseMixedPairEquiv_isometry
