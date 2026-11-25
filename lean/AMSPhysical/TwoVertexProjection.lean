import TwoVertexTensorEmbedding
import BilinearMetricAdjoint

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical

/-- Literal coordinate restriction to the first two occupation vertices.
This map is defined without a quantum parameter or an overlap candidate. -/
def twoVertexProjection (n : ℕ) (hn : 0<n) (L : ℕ) :
    quantumOccupationSpace ℝ (Fin (n+1)) L →ₗ[ℝ] finiteWeightSpace (K:=ℝ) L :=
  (standardWeightBasis (K:=ℝ) L).equivFun.symm.toLinearMap.comp
    (LinearMap.pi (fun k : Fin (L+1) =>
      (LinearMap.proj (twoVertexOccupation n hn L k)).comp
        (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).equivFun.toLinearMap))

theorem twoVertexProjection_coordinate (n : ℕ) (hn : 0<n) (L : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) L) (k : Fin (L+1)) :
    (standardWeightBasis (K:=ℝ) L).equivFun (twoVertexProjection n hn L v) k=
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).equivFun v (twoVertexOccupation n hn L k) := by
  unfold twoVertexProjection
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,LinearMap.pi_apply,LinearMap.proj_apply]

theorem twoVertexEmbedding_coordinate (n : ℕ) (hn : 0<n) (L : ℕ)
    (v : finiteWeightSpace (K:=ℝ) L) (k : Fin (L+1)) :
    (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).equivFun (twoVertexEmbedding n hn L v)
      (twoVertexOccupation n hn L k)=(standardWeightBasis (K:=ℝ) L).equivFun v k := by
  have he : ((LinearMap.proj (twoVertexOccupation n hn L k)).comp
      ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L).equivFun.toLinearMap.comp (twoVertexEmbedding n hn L)))=
    (LinearMap.proj k).comp (standardWeightBasis (K:=ℝ) L).equivFun.toLinearMap := by
    apply (standardWeightBasis (K:=ℝ) L).ext
    intro j
    simp only [LinearMap.comp_apply,LinearMap.proj_apply,LinearEquiv.coe_coe,twoVertexEmbedding_basis,
      Module.Basis.equivFun_apply,Module.Basis.repr_self,Finsupp.single_apply]
    simp only [(twoVertexOccupation_injective n hn L).eq_iff]
  exact DFunLike.congr_fun he v

theorem twoVertexProjection_embedding (n : ℕ) (hn : 0<n) (L : ℕ) (v : finiteWeightSpace (K:=ℝ) L) :
    twoVertexProjection n hn L (twoVertexEmbedding n hn L v)=v := by
  apply (standardWeightBasis (K:=ℝ) L).equivFun.injective
  funext k
  rw [twoVertexProjection_coordinate,twoVertexEmbedding_coordinate]

end AMSPhysical
#print axioms AMSPhysical.twoVertexProjection_embedding
