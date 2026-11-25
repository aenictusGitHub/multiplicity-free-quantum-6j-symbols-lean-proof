import RankTwoTypeIITripleEquivalence
import StandardWeightReversal
import TwoVertexTripleProjection

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem occupationReflection_twoVertex_rankTwo (L:ℕ) (k:Fin (L+1)):
    occupationReflection 1 L (twoVertexOccupation 1 (by omega) L k)=
      twoVertexOccupation 1 (by omega) L k.rev := by
  apply Subtype.ext
  funext j
  fin_cases j
  · change (twoVertexOccupation 1 (by omega) L k).val (secondVertex 1 (by omega))=
      (twoVertexOccupation 1 (by omega) L k.rev).val 0
    rw [twoVertexOccupation_second,twoVertexOccupation_first]
    simp only [Fin.val_rev]
    have hk:=k.isLt
    omega
  · change (twoVertexOccupation 1 (by omega) L k).val 0=
      (twoVertexOccupation 1 (by omega) L k.rev).val (secondVertex 1 (by omega))
    rw [twoVertexOccupation_first,twoVertexOccupation_second]
    simp only [Fin.val_rev]
    omega

theorem rankTwoOppositeEquiv_eq_reversal (L:ℕ):
    (rankTwoOppositeEquiv L).toLinearMap=
      (twoVertexEmbedding 1 (by omega) L).comp (standardWeightReversal L).toLinearMap := by
  apply (standardWeightBasis (K:=ℝ) L).ext
  intro k
  change quantumOccupationReflection 1 L ((rankTwoSymmetricEquiv L).toLinearMap (standardWeightBasis L k))=_
  rw [rankTwoSymmetricEquiv_eq_embedding,twoVertexEmbedding_basis,quantumOccupationReflection_basis,
    occupationReflection_twoVertex_rankTwo]
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,standardWeightReversal_basis,twoVertexEmbedding_basis]

theorem rankTwoOppositeEquiv_projection (L:ℕ) (v:finiteWeightSpace (K:=ℝ) L):
    twoVertexProjection 1 (by omega) L (rankTwoOppositeEquiv L v)=standardWeightReversal L v := by
  change twoVertexProjection 1 (by omega) L ((rankTwoOppositeEquiv L).toLinearMap v)=_
  rw [rankTwoOppositeEquiv_eq_reversal,LinearMap.comp_apply,twoVertexProjection_embedding]
  rfl

theorem rankTwoTypeIITripleEquiv_boundary (a b c:ℕ) (v:RealQuantumTripleSpace a b c):
    twoVertexTripleProjection 1 (by omega) a b c (rankTwoTypeIITripleEquiv a b c v)=
      standardTypeIIBoundaryEquiv a b c v := by
  rw [standardTypeIIBoundaryEquiv_before_assoc]
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw => simp only [map_add,hv,hw]
  | tmul u v =>
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add u u' hu hu' => simp only [TensorProduct.add_tmul,map_add,hu,hu']
    | tmul x y =>
      simp only [rankTwoTypeIITripleEquiv,rankTwoRightTypeIITripleEquiv,rankTwoMixedPairEquiv,
        LinearEquiv.trans_apply,TensorProduct.assoc_tmul,TensorProduct.congr_tmul,
        twoVertexTripleProjection,twoVertexTensorProjection,TensorProduct.map_tmul,
        LinearMap.id_apply,LinearEquiv.coe_coe,rankTwoOppositeEquiv_projection]
      change (twoVertexProjection 1 (by omega) a ((rankTwoSymmetricEquiv a).toLinearMap x)) ⊗ₜ[ℝ]
        ((twoVertexProjection 1 (by omega) b ((rankTwoSymmetricEquiv b).toLinearMap y)) ⊗ₜ[ℝ]
          standardWeightReversal c v)=_
      rw [rankTwoSymmetricEquiv_eq_embedding,rankTwoSymmetricEquiv_eq_embedding,
        twoVertexProjection_embedding,twoVertexProjection_embedding]

end AMSPhysical
#print axioms AMSPhysical.rankTwoTypeIITripleEquiv_boundary
