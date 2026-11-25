import TwoVertexPairProjection
import QuantumTensorMetric

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem twoVertexTensorProjection_adjoint (q : ℝ) (hq : 0<q) (hq1 : q≠1)
    (n : ℕ) (hn : 0<n) (l m : ℕ)
    (v : finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m)
    (w : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :
    symmetricTensorBilin q n l m (twoVertexTensorEmbedding n hn l m v) w=
      quantumTensorBilin q l m v (twoVertexTensorProjection n hn l m w) := by
  have he : (symmetricTensorBilin q n l m).comp (twoVertexTensorEmbedding n hn l m)=
      (quantumTensorBilin q l m).compl₂ (twoVertexTensorProjection n hn l m) := by
    apply ((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)).ext
    intro ij
    apply ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)).ext
    intro p
    change symmetricTensorBilin q n l m (twoVertexTensorEmbedding n hn l m
      (((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)) ij))
      (((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)) p)=
      quantumTensorBilin q l m (((standardWeightBasis (K:=ℝ) l).tensorProduct (standardWeightBasis (K:=ℝ) m)) ij)
        (twoVertexTensorProjection n hn l m
          (((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)) p))
    simp only [Module.Basis.tensorProduct_apply',twoVertexTensorEmbedding,twoVertexTensorProjection,TensorProduct.map_tmul]
    unfold symmetricTensorBilin quantumTensorBilin
    rw [tensorWeightedBilin_tmul,tensorWeightedBilin_tmul]
    change occupationCompactBilin q n l (twoVertexEmbedding n hn l (standardWeightBasis l ij.1))
      (quantumOccupationBasis (K:=ℝ) l p.1)*
      occupationCompactBilin q n m (twoVertexEmbedding n hn m (standardWeightBasis m ij.2))
        (quantumOccupationBasis (K:=ℝ) m p.2)=
      quantumBilin q l (standardWeightBasis l ij.1) (twoVertexProjection n hn l (quantumOccupationBasis (K:=ℝ) l p.1))*
      quantumBilin q m (standardWeightBasis m ij.2) (twoVertexProjection n hn m (quantumOccupationBasis (K:=ℝ) m p.2))
    rw [twoVertexProjection_adjoint q hq hq1,twoVertexProjection_adjoint q hq hq1]
  exact DFunLike.congr_fun (DFunLike.congr_fun he v) w

end AMSPhysical
#print axioms AMSPhysical.twoVertexTensorProjection_adjoint
