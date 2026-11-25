import GlobalMixedOrientationBoundary
import RankTwoTypeIFirstBoundary
import StandardBoundaryCreationCoordinate

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem occupationHighestFunctional_basis (n L : ℕ) (x : occupationWeights (Fin (n+1)) L) :
    occupationHighestFunctional n L (quantumOccupationBasis (K:=ℝ) L x)=
      if x=highestOccupation n L then 1 else 0 := by
  simp only [occupationHighestFunctional,LinearMap.comp_apply,Finsupp.lapply_apply,
    Submodule.subtype_apply,quantumOccupationBasis_coe,Finsupp.single_apply,Subtype.ext_iff]

theorem occupationHighestFunctional_eq_repr (n L : ℕ) (v : quantumOccupationSpace ℝ (Fin (n+1)) L) :
    occupationHighestFunctional n L v = (quantumOccupationBasis (K:=ℝ) L).repr v (highestOccupation n L) := by
  have he : occupationHighestFunctional n L =
      (Finsupp.lapply (highestOccupation n L)).comp (quantumOccupationBasis (K:=ℝ) L).repr.toLinearMap := by
    apply (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).ext
    intro x
    simp only [occupationHighestFunctional_basis,LinearMap.comp_apply,LinearEquiv.coe_coe,
      Finsupp.lapply_apply,Module.Basis.repr_self,Finsupp.single_apply]
  exact DFunLike.congr_fun he v

def physicalAllFirstFunctional (n a b c : ℕ) : quantumOccupationTripleSpace n a b c →ₗ[ℝ] ℝ :=
  (Finsupp.lapply (highestOccupation n a,highestOccupation n b,highestOccupation n c)).comp
    (occupationTripleBasis n a b c).repr.toLinearMap

theorem physicalAllFirstFunctional_tmul (n a b c : ℕ)
    (x : quantumOccupationSpace ℝ (Fin (n+1)) a)
    (y : quantumOccupationSpace ℝ (Fin (n+1)) b)
    (z : quantumOccupationSpace ℝ (Fin (n+1)) c) :
    physicalAllFirstFunctional n a b c (x ⊗ₜ[ℝ] (y ⊗ₜ[ℝ] z)) =
      occupationHighestFunctional n a x * (occupationHighestFunctional n b y * occupationHighestFunctional n c z) := by
  simp only [physicalAllFirstFunctional,LinearMap.comp_apply,Finsupp.lapply_apply,
    LinearEquiv.coe_coe,occupationTripleBasis,Module.Basis.tensorProduct_repr_tmul_apply,
    occupationHighestFunctional_eq_repr,smul_eq_mul]
  ring

theorem physicalTypeIFirstBoundary_eq_allFirst (n a b c : ℕ) :
    physicalTypeIFirstBoundary n a b 0 c=physicalAllFirstFunctional n a b c := by
  apply LinearMap.ext
  intro v
  unfold physicalTypeIFirstBoundary
  simp only [LinearMap.comp_apply,Finsupp.lapply_apply,Nat.add_zero,
    cupFirstBoundaryPoint,Nat.cast_zero,add_zero,Pi.single_zero,zero_add]
  change occupationTripleCoefficients n a b c v
    (occupationTripleEmbedding n a b c (highestOccupation n a,highestOccupation n b,highestOccupation n c)) = _
  exact injectedBasisCoefficients_repr (occupationTripleBasis n a b c) (occupationTripleEmbedding n a b c)
    (occupationTripleEmbedding_injective n a b c) v _

theorem physicalAllFirstFunctional_mixed (n a p s : ℕ) :
    physicalAllFirstFunctional n a p s =
      (mixedFirstBoundaryFunctional n p s).comp
        (tensorFirstFunctional (occupationHighestFunctional n a)) := by
  apply TensorProduct.ext'
  intro x v
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw => simp only [TensorProduct.tmul_add,map_add,hv,hw]
  | tmul y z =>
    simp only [LinearMap.comp_apply,tensorFirstFunctional_tmul,map_smul,smul_eq_mul,
      mixedFirstBoundaryFunctional,physicalAllFirstFunctional_tmul]

theorem physicalAllFirstFunctional_reverseMixed (n a p s : ℕ) :
    physicalAllFirstFunctional n a s p =
      (reverseMixedFirstBoundaryFunctional n p s).comp
        (tensorFirstFunctional (occupationHighestFunctional n a)) := by
  apply TensorProduct.ext'
  intro x v
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw => simp only [TensorProduct.tmul_add,map_add,hv,hw]
  | tmul y z =>
    simp only [LinearMap.comp_apply,tensorFirstFunctional_tmul,tensorLastFunctional_tmul,map_smul,smul_eq_mul,
      reverseMixedFirstBoundaryFunctional,physicalAllFirstFunctional_tmul]
    ring

theorem twoVertexProjection_highest_coordinate (n : ℕ) (hn : 0<n) (L : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) L) :
    (standardWeightBasis (K:=ℝ) L).repr (twoVertexProjection n hn L v) 0 =
      occupationHighestFunctional n L v := by
  change (standardWeightBasis (K:=ℝ) L).equivFun (twoVertexProjection n hn L v) 0 = _
  rw [twoVertexProjection_coordinate,twoVertexOccupation_zero,occupationHighestFunctional_eq_repr]
  rfl

theorem physicalAllFirstFunctional_projection (n : ℕ) (hn : 0<n) (a b c : ℕ) :
    (standardBoundaryCoordinate a b c 0 0).comp (twoVertexTripleProjection n hn a b c) =
      physicalAllFirstFunctional n a b c := by
  apply TensorProduct.ext'
  intro x v
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw => simp only [TensorProduct.tmul_add,map_add,hv,hw]
  | tmul y z =>
    simp only [LinearMap.comp_apply,twoVertexTripleProjection,twoVertexTensorProjection,TensorProduct.map_tmul]
    rw [standardBoundaryCoordinate,dif_pos (by omega),dif_pos (by omega)]
    simp only [LinearMap.comp_apply,Finsupp.lapply_apply,LinearEquiv.coe_coe,
      Module.Basis.tensorProduct_repr_tmul_apply,smul_eq_mul]
    simp only [Fin.mk_zero',twoVertexProjection_highest_coordinate]
    rw [physicalAllFirstFunctional_tmul]
    ring

end AMSPhysical
#print axioms AMSPhysical.physicalAllFirstFunctional_projection
