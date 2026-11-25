import OccupationTensorHighestSlices
import GlobalReverseMixedPairTransfers
import ActualVertexTransport

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem occupationCoordinate_reflection (n L : ℕ) (x : occupationWeights (Fin (n+1)) L)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) L) :
    occupationCoordinate n L (occupationReflection n L x) (quantumOccupationReflection n L v)=
      occupationCoordinate n L x v := by
  have he : (occupationCoordinate n L (occupationReflection n L x)).comp
      (quantumOccupationReflection n L).toLinearMap=occupationCoordinate n L x := by
    apply (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).ext
    intro y
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,quantumOccupationReflection_basis,
      occupationCoordinate_eq_repr,Module.Basis.repr_self,Finsupp.single_apply,
      (occupationReflection_involutive n L).injective.eq_iff]
  exact DFunLike.congr_fun he v

theorem occupationAugmentation_reflection (n L : ℕ) (v : quantumOccupationSpace ℝ (Fin (n+1)) L) :
    occupationAugmentation n L (quantumOccupationReflection n L v)=occupationAugmentation n L v := by
  have he : (occupationAugmentation n L).comp (quantumOccupationReflection n L).toLinearMap=
      occupationAugmentation n L := by
    apply (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).ext
    intro y
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,quantumOccupationReflection_basis,
      occupationAugmentation_basis]
  exact DFunLike.congr_fun he v

theorem normalizedReverseMixedHighest_augmentation_pos (q : ℝ) (hq : 0<q)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : MixedFusionIndex l m) :
    0 < occupationAugmentation n m
      (tensorFirstFunctional (occupationCoordinate n l (lowestOccupation n l))
        (normalizedReverseMixedFusionHighestAt q n l m r)) := by
  rw [normalizedReverseMixedFusionHighest_reflection]
  have he:=tensorBoundary_map (occupationCoordinate n l (highestOccupation n l)) (occupationAugmentation n m)
    (occupationCoordinate n l (lowestOccupation n l)) (occupationAugmentation n m)
    (quantumOccupationReflection n l).toLinearMap (quantumOccupationReflection n m).toLinearMap
    (by intro v;rw [← occupationReflection_highest n l];exact occupationCoordinate_reflection n l _ v)
    (occupationAugmentation_reflection n m) (normalizedMixedFusionHighestAt q n l m r)
  change occupationAugmentation n m
    (tensorFirstFunctional (occupationCoordinate n l (lowestOccupation n l))
      (mixedReflection n l m (normalizedMixedFusionHighestAt q n l m r))) = _ at he
  rw [he]
  exact normalizedMixedHighest_augmentation_pos q hq n hn l m r

end AMSPhysical
#print axioms AMSPhysical.normalizedReverseMixedHighest_augmentation_pos
