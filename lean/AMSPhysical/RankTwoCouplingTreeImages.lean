import RankTwoMixedTripleEquivalence
import RankTwoReverseClebschChannels

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem rankTwoMixedTripleEquiv_left_tensor (l m c : ℕ) (v : RealQuantumTripleSpace l m c) :
    rankTwoMixedTripleEquiv l m c v=(TensorProduct.assoc ℝ _ _ _)
      (TensorProduct.map (rankTwoMixedPairEquiv l m).toLinearMap (rankTwoSymmetricEquiv c).toLinearMap v) := by
  have he : (rankTwoMixedTripleEquiv l m c).toLinearMap=
      (TensorProduct.assoc ℝ _ _ _).toLinearMap.comp
        (TensorProduct.map (rankTwoMixedPairEquiv l m).toLinearMap (rankTwoSymmetricEquiv c).toLinearMap) := by
    apply TensorProduct.ext'
    intro xy z
    induction xy using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [rankTwoMixedTripleEquiv,rankTwoRightMixedTripleEquiv,rankTwoMixedPairEquiv,
        rankTwoReverseMixedPairEquiv,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.trans_apply,
        TensorProduct.assoc_tmul,TensorProduct.map_tmul,TensorProduct.congr_tmul]
    | add x y hx hy => simpa only [TensorProduct.add_tmul,map_add,LinearMap.comp_apply] using congrArg₂ (·+·) hx hy
  exact DFunLike.congr_fun he v

theorem rankTwoLeftTree_image (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m c : ℕ)
    (r : MixedFusionIndex l m) (s : Fin (min (coupledLabel l m r) c+1))
    (v : RealQuantumSpace (coupledLabel (coupledLabel l m r) c s)) :
    rankTwoMixedTripleEquiv l m c (quantumLeftTreeMap q hq hq1 l m c r s v)=
      (TensorProduct.assoc ℝ _ _ _)
        (TensorProduct.map (rankTwoMixedClebsch q hq hq1 l m r) (rankTwoSymmetricEquiv c).toLinearMap
          (unitaryQuantumClebschMap q hq hq1 (coupledLabel l m r) c s v)) := by
  rw [rankTwoMixedTripleEquiv_left_tensor]
  unfold quantumLeftTreeMap
  simp only [LinearMap.comp_apply]
  rw [← LinearMap.comp_apply,← TensorProduct.map_comp]
  rfl

theorem rankTwoRightTree_image (q : ℝ) (hq : 0<q) (hq1 : q≠1) (l m c : ℕ)
    (r : MixedFusionIndex m c) (s : Fin (min l (coupledLabel m c r)+1))
    (v : RealQuantumSpace (coupledLabel l (coupledLabel m c r) s)) :
    rankTwoMixedTripleEquiv l m c (quantumRightTreeMap q hq hq1 l m c r s v)=
      TensorProduct.map (rankTwoSymmetricEquiv l).toLinearMap (rankTwoReverseMixedClebsch q hq hq1 m c r)
        (unitaryQuantumClebschMap q hq hq1 l (coupledLabel m c r) s v) := by
  unfold rankTwoMixedTripleEquiv quantumRightTreeMap
  simp only [LinearEquiv.trans_apply,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
  change TensorProduct.map (rankTwoSymmetricEquiv l).toLinearMap (rankTwoReverseMixedPairEquiv m c).toLinearMap
    (TensorProduct.map LinearMap.id (unitaryQuantumClebschMap q hq hq1 m c r)
      (unitaryQuantumClebschMap q hq hq1 l (coupledLabel m c r) s v))=_
  rw [← LinearMap.comp_apply,← TensorProduct.map_comp]
  rfl

end AMSPhysical
#print axioms AMSPhysical.rankTwoLeftTree_image
#print axioms AMSPhysical.rankTwoRightTree_image
