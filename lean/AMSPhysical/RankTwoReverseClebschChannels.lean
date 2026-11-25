import RankTwoMixedClebschChannels
import QuantumReflectionInvolutive
import QuantumReverseFusion

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem rankTwoReverseMixedPairEquiv_reflection (l m : ℕ)
    (v : finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) :
    rankTwoReverseMixedPairEquiv l m v=mixedReflection 1 l m (rankTwoMixedPairEquiv l m v) := by
  have he : (rankTwoReverseMixedPairEquiv l m).toLinearMap=
      (mixedReflection 1 l m).toLinearMap.comp (rankTwoMixedPairEquiv l m).toLinearMap := by
    apply TensorProduct.ext'
    intro x y
    simp only [rankTwoReverseMixedPairEquiv,rankTwoMixedPairEquiv,mixedReflection,
      LinearMap.comp_apply,LinearEquiv.coe_coe,TensorProduct.congr_tmul,
      rankTwoOppositeEquiv,LinearEquiv.trans_apply,quantumOccupationReflection_twice]
  exact DFunLike.congr_fun he v

def rankTwoReverseMixedClebsch (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ) (r : MixedFusionIndex l m) :
    finiteWeightSpace (K:=ℝ) (coupledLabel l m r) →ₗ[ℝ]
      quantumOccupationSpace ℝ (Fin 2) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin 2) m :=
  (rankTwoReverseMixedPairEquiv l m).toLinearMap.comp (unitaryQuantumClebschMap q hq hq1 l m r)

theorem rankTwoReverseMixedClebsch_channel (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m : ℕ) (r : MixedFusionIndex l m)
    (v : finiteWeightSpace (K:=ℝ) (coupledLabel l m r)) :
    rankTwoReverseMixedClebsch q hq hq1 l m r v∈
      reverseMixedFusionChannelAt q (ne_of_gt hq) (qInteger_denominator_ne_zero q hq hq1) 1 l m r := by
  change rankTwoReverseMixedPairEquiv l m (unitaryQuantumClebschMap q hq hq1 l m r v)∈_
  rw [rankTwoReverseMixedPairEquiv_reflection,← reverseMixedFusionChannelAt_map]
  exact ⟨rankTwoMixedClebsch q hq hq1 l m r v,rankTwoMixedClebsch_channel q hq hq1 l m r v,rfl⟩

end AMSPhysical
#print axioms AMSPhysical.rankTwoReverseMixedClebsch_channel
