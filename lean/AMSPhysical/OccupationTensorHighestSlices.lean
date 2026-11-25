import MixedSymHighestBoundary
import ActualAMSCarriers
import TwoRowHighestBoundary

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem occupationCoordinate_eq_repr (n L : ℕ) (x : occupationWeights (Fin (n+1)) L)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) L) :
    occupationCoordinate n L x v=(quantumOccupationBasis (K:=ℝ) L).repr v x := by
  have he : occupationCoordinate n L x =
      (Finsupp.lapply x).comp (quantumOccupationBasis (K:=ℝ) L).repr.toLinearMap := by
    apply (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).ext
    intro y
    simp [occupationCoordinate,quantumOccupationBasis_coe,Finsupp.single_apply,Subtype.ext_iff]
  exact DFunLike.congr_fun he v

theorem occupationCoordinate_tensorFirst (n l m : ℕ)
    (x : occupationWeights (Fin (n+1)) l) (y : occupationWeights (Fin (n+1)) m)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ]
      quantumOccupationSpace ℝ (Fin (n+1)) m) :
    occupationCoordinate n m y (tensorFirstFunctional (occupationCoordinate n l x) v) =
      occupationTensorCoefficients n l m v (x.val,y.val) := by
  rw [occupationTensorCoefficients_repr]
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw => simp only [map_add,Finsupp.add_apply,hv,hw]
  | tmul v w =>
    simp only [tensorFirstFunctional_tmul,map_smul,smul_eq_mul,occupationCoordinate_eq_repr,
      Module.Basis.tensorProduct_repr_tmul_apply]
    ring

theorem occupationFirstProjection_of_boundary (n l m : ℕ)
    (x : occupationWeights (Fin (n+1)) l) (y : occupationWeights (Fin (n+1)) m)
    (a : ℝ) (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ]
      quantumOccupationSpace ℝ (Fin (n+1)) m)
    (hV : ∀ z : occupationWeights (Fin (n+1)) m,
      occupationTensorCoefficients n l m v (x.val,z.val)=a*(if y=z then 1 else 0)) :
    tensorFirstFunctional (occupationCoordinate n l x) v=a • quantumOccupationBasis (K:=ℝ) m y := by
  apply (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m).repr.injective
  apply Finsupp.ext
  intro z
  rw [← occupationCoordinate_eq_repr,occupationCoordinate_tensorFirst,hV]
  simp only [map_smul,Finsupp.smul_apply,smul_eq_mul,Module.Basis.repr_self,Finsupp.single_apply]

theorem symmetric_highest_functional_coordinate (q : ℝ) (hq : 0<q) (n L : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) L) :
    occupationCompactBilin q n L (quantumOccupationBasis (K:=ℝ) L (highestOccupation n L)) v =
      occupationCoordinate n L (highestOccupation n L) v := by
  rw [occupationCompactBilin_symm]
  change finiteWeightedPair (occupationCompactWeight q n L)
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).equivFun.toLinearMap v
    (quantumOccupationBasis (K:=ℝ) L (highestOccupation n L)) = _
  rw [finiteWeightedPair_basis_right,occupationCompactWeight_highest q hq,one_mul,
    occupationCoordinate_eq_repr]
  rfl

theorem opposite_highest_functional_coordinate (q : ℝ) (hq : 0<q) (n L : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) L) :
    occupationOppositeBilin q n L (quantumOccupationBasis (K:=ℝ) L (lowestOccupation n L)) v =
      occupationCoordinate n L (lowestOccupation n L) v := by
  rw [occupationOppositeBilin_symm]
  change finiteWeightedPair (occupationOppositeWeight q n L)
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).equivFun.toLinearMap v
    (quantumOccupationBasis (K:=ℝ) L (lowestOccupation n L)) = _
  rw [finiteWeightedPair_basis_right,occupationOppositeWeight_highest q hq,one_mul,
    occupationCoordinate_eq_repr]
  rfl

theorem normalizedMixedHighest_augmentation_pos (q : ℝ) (hq : 0<q)
    (n : ℕ) (hn : 0<n) (l m : ℕ) (r : MixedFusionIndex l m) :
    0 < occupationAugmentation n m (tensorFirstFunctional (occupationCoordinate n l (highestOccupation n l))
      (normalizedMixedFusionHighestAt q n l m r)) := by
  have hp:=occupationFirstProjection_of_boundary n l m (highestOccupation n l)
    (mixedBoundaryAt n l m r) (Real.sqrt (mixedCouplingNormClosed q n (l-r.val) (m-r.val) r.val))⁻¹
    (normalizedMixedFusionHighestAt q n l m r) (by
      intro z
      simp only [normalizedMixedFusionHighestAt,map_smul,Finsupp.smul_apply,smul_eq_mul,
        mixedFusionHighestAt_boundary q hq n hn])
  rw [hp,map_smul,occupationAugmentation_basis,smul_eq_mul,mul_one]
  exact inv_pos.mpr (Real.sqrt_pos.mpr (mixedCouplingNormClosed_pos q hq n _ _ _))

theorem normalizedTwoRowHighest_augmentation_pos (q : ℝ) (hq : 0<q)
    (n : ℕ) (hn : 0<n) (l m r : ℕ) (hl : r≤l) (hm : r≤m) :
    0 < occupationAugmentation n m (tensorFirstFunctional (occupationCoordinate n l (highestOccupation n l))
      (normalizedTwoRowHighest q n hn l m r hl hm)) := by
  have hp:=occupationFirstProjection_of_boundary n l m (highestOccupation n l)
    (twoVertexOccupation n hn m ⟨r,by omega⟩) (Real.sqrt (couplingNormClosed q (l-r) (m-r) r))⁻¹
    (normalizedTwoRowHighest q n hn l m r hl hm) (by
      intro z
      simp only [normalizedTwoRowHighest,map_smul,Finsupp.smul_apply,smul_eq_mul,
        twoRowHighest_boundary_coefficient])
  rw [hp,map_smul,occupationAugmentation_basis,smul_eq_mul,mul_one]
  exact inv_pos.mpr (Real.sqrt_pos.mpr (couplingNormClosed_pos q hq _ _ _))

end AMSPhysical
#print axioms AMSPhysical.normalizedMixedHighest_augmentation_pos
#print axioms AMSPhysical.normalizedTwoRowHighest_augmentation_pos
