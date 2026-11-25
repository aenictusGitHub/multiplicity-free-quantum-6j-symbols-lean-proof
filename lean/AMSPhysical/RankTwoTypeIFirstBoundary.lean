import RankTwoTypeIIBoundary
import RankTwoMixedTripleEquivalence
import GlobalCupBoundaryTransport
import OccupationTripleBasisProperties

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

def rankTwoMixedTripleIndex (l m c : ℕ)
    (p : (Fin (l+1) × Fin (m+1)) × Fin (c+1)) : OccupationTripleIndex 1 l m c :=
  (twoVertexOccupation 1 (by omega) l p.1.1,
    twoVertexOccupation 1 (by omega) m p.1.2.rev,
    twoVertexOccupation 1 (by omega) c p.2)

theorem rankTwoMixedTripleIndex_injective (l m c : ℕ) :
    Function.Injective (rankTwoMixedTripleIndex l m c) := by
  intro p z he
  have h1:=twoVertexOccupation_injective 1 (by omega) l (congrArg Prod.fst he)
  have h2:=twoVertexOccupation_injective 1 (by omega) m (congrArg (fun x=>x.2.1) he)
  have h3:=twoVertexOccupation_injective 1 (by omega) c (congrArg (fun x=>x.2.2) he)
  have h2':p.1.2=z.1.2 := by simpa using congrArg Fin.rev h2
  exact Prod.ext (Prod.ext h1 h2') h3

theorem rankTwoMixedTripleEquiv_basis (l m c : ℕ)
    (p : (Fin (l+1) × Fin (m+1)) × Fin (c+1)) :
    rankTwoMixedTripleEquiv l m c
      ((((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).tensorProduct
        (standardWeightBasis (K:=ℝ) c)) p) =
      occupationTripleBasis 1 l m c (rankTwoMixedTripleIndex l m c p) := by
  simp only [Module.Basis.tensorProduct_apply',rankTwoMixedTripleEquiv,
    rankTwoRightMixedTripleEquiv,rankTwoReverseMixedPairEquiv,LinearEquiv.trans_apply,
    TensorProduct.assoc_tmul,TensorProduct.congr_tmul]
  change ((rankTwoSymmetricEquiv l).toLinearMap (standardWeightBasis l p.1.1)) ⊗ₜ[ℝ]
    (((rankTwoOppositeEquiv m).toLinearMap (standardWeightBasis m p.1.2)) ⊗ₜ[ℝ]
      ((rankTwoSymmetricEquiv c).toLinearMap (standardWeightBasis c p.2))) = _
  rw [rankTwoSymmetricEquiv_eq_embedding,rankTwoSymmetricEquiv_eq_embedding,
    rankTwoOppositeEquiv_eq_reversal]
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,standardWeightReversal_basis,twoVertexEmbedding_basis]
  simp only [occupationTripleBasis,rankTwoMixedTripleIndex,Module.Basis.tensorProduct_apply']

theorem rankTwoMixedTripleEquiv_coefficient (l m c : ℕ) (v : RealQuantumTripleSpace l m c)
    (p : (Fin (l+1) × Fin (m+1)) × Fin (c+1)) :
    occupationTripleCoefficients 1 l m c (rankTwoMixedTripleEquiv l m c v)
      (occupationTripleEmbedding 1 l m c (rankTwoMixedTripleIndex l m c p)) =
      (((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).tensorProduct
        (standardWeightBasis (K:=ℝ) c)).repr v p := by
  classical
  have he : ((Finsupp.lapply (occupationTripleEmbedding 1 l m c (rankTwoMixedTripleIndex l m c p))).comp
      ((occupationTripleCoefficients 1 l m c).comp (rankTwoMixedTripleEquiv l m c).toLinearMap)) =
      (Finsupp.lapply p).comp
        (((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).tensorProduct
          (standardWeightBasis (K:=ℝ) c)).repr.toLinearMap := by
    apply (((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).tensorProduct
      (standardWeightBasis (K:=ℝ) c)).ext
    intro z
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,rankTwoMixedTripleEquiv_basis,
      occupationTripleCoefficients_basis,Module.Basis.repr_self,Finsupp.lapply_apply,Finsupp.single_apply]
    have hij : occupationTripleEmbedding 1 l m c (rankTwoMixedTripleIndex l m c z) =
        occupationTripleEmbedding 1 l m c (rankTwoMixedTripleIndex l m c p) ↔ z=p :=
      ((occupationTripleEmbedding_injective 1 l m c).comp (rankTwoMixedTripleIndex_injective l m c)).eq_iff
    simp only [hij]
  exact DFunLike.congr_fun he v

def physicalTypeIFirstBoundary (n l m h c : ℕ) : quantumOccupationTripleSpace n l (m+h) c →ₗ[ℝ] ℝ :=
  (Finsupp.lapply (cupFirstBoundaryPoint n l h c m 0)).comp (occupationTripleCoefficients n l (m+h) c)

theorem rankTwoMixedTripleEquiv_first_boundary (l m h c : ℕ) (v : RealQuantumTripleSpace l (m+h) c) :
    physicalTypeIFirstBoundary 1 l m h c (rankTwoMixedTripleEquiv l (m+h) c v) =
      (((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) (m+h))).tensorProduct
        (standardWeightBasis (K:=ℝ) c)).repr v ((0,⟨m,by omega⟩),0) := by
  have he : occupationTripleEmbedding 1 l (m+h) c
      (rankTwoMixedTripleIndex l (m+h) c ((0,⟨m,by omega⟩),0)) =
      cupFirstBoundaryPoint 1 l h c m 0 := by
    simp only [occupationTripleEmbedding,rankTwoMixedTripleIndex,twoVertexOccupation_zero]
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext j
        fin_cases j <;> simp [twoVertexOccupation,cupFirstBoundaryPoint,secondVertex,highestOccupation,Fin.val_rev,Pi.single_apply]
      · rfl
  change occupationTripleCoefficients 1 l (m+h) c (rankTwoMixedTripleEquiv l (m+h) c v) _ = _
  rw [← he]
  exact rankTwoMixedTripleEquiv_coefficient l (m+h) c v ((0,⟨m,by omega⟩),0)

end AMSPhysical
#print axioms AMSPhysical.rankTwoMixedTripleEquiv_first_boundary
