import TwoVertexTripleProjection
import RankTwoSymmetricEquivalence
import QuantumTripleMetric

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem twoVertexProjection_rankTwo (L : ℕ) :
    twoVertexProjection 1 (by omega) L=(rankTwoSymmetricEquiv L).symm.toLinearMap := by
  apply LinearMap.ext
  intro w
  obtain ⟨v,rfl⟩:=(rankTwoSymmetricEquiv L).surjective w
  rw [LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
  change twoVertexProjection 1 (by omega) L ((rankTwoSymmetricEquiv L).toLinearMap v)=v
  rw [rankTwoSymmetricEquiv_eq_embedding,twoVertexProjection_embedding]

def rankTwoUnderlyingTripleProjectionEquiv (a b c : ℕ) :
    quantumOccupationTripleSpace 1 a b c ≃ₗ[ℝ]
      (finiteWeightSpace (K:=ℝ) a ⊗[ℝ] (finiteWeightSpace (K:=ℝ) b ⊗[ℝ] finiteWeightSpace (K:=ℝ) c)) :=
  TensorProduct.congr (rankTwoSymmetricEquiv a).symm
    (TensorProduct.congr (rankTwoSymmetricEquiv b).symm (rankTwoSymmetricEquiv c).symm)

theorem twoVertexTripleProjection_rankTwo (a b c : ℕ) :
    twoVertexTripleProjection 1 (by omega) a b c=(rankTwoUnderlyingTripleProjectionEquiv a b c).toLinearMap := by
  unfold twoVertexTripleProjection twoVertexTensorProjection
  rw [twoVertexProjection_rankTwo,twoVertexProjection_rankTwo,twoVertexProjection_rankTwo]
  rfl

theorem twoVertexTripleProjection_rankTwo_injective (a b c : ℕ) :
    Function.Injective (twoVertexTripleProjection 1 (by omega) a b c) := by
  rw [twoVertexTripleProjection_rankTwo]
  exact (rankTwoUnderlyingTripleProjectionEquiv a b c).injective

end AMSPhysical
#print axioms AMSPhysical.twoVertexTripleProjection_rankTwo_injective
