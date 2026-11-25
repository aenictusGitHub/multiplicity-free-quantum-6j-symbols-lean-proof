import TwoVertexShiftSupport
import TwoVertexPairProjection
import QuantumMixedFiniteCreation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem twoVertexProjection_basis_boundary (n : ℕ) (hn : 0<n) (L : ℕ) (k : Fin (L+1)) :
    twoVertexProjection n hn L (quantumOccupationBasis (K:=ℝ) L (twoVertexOccupation n hn L k))=
      standardWeightBasis (K:=ℝ) L k := by
  rw [← twoVertexEmbedding_basis]
  exact twoVertexProjection_embedding n hn L _

theorem mixedFiniteCreation_projection_left_outside (q : ℝ) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (x : occupationWeights (Fin (n+1)) l) (y : occupationWeights (Fin (n+1)) m)
    (hx : ¬∃ k : Fin (l+1),x=twoVertexOccupation n hn l k) :
    twoVertexTensorProjection n hn (l+1) (m+1)
      (mixedFiniteCreation q n l m (quantumOccupationBasis (K:=ℝ) l x ⊗ₜ[ℝ] quantumOccupationBasis (K:=ℝ) m y))=0 := by
  rw [mixedFiniteCreation_basis,map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  simp only [map_smul,twoVertexTensorProjection,TensorProduct.map_tmul]
  rw [twoVertexProjection_basis_outside n hn (l+1) (shiftedOccupation n l 1 j x)
    (shiftedOccupation_outside_twoVertex n hn l 1 x hx j),TensorProduct.zero_tmul,smul_zero]

theorem mixedFiniteCreation_projection_right_outside (q : ℝ) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (x : occupationWeights (Fin (n+1)) l) (y : occupationWeights (Fin (n+1)) m)
    (hy : ¬∃ k : Fin (m+1),y=twoVertexOccupation n hn m k) :
    twoVertexTensorProjection n hn (l+1) (m+1)
      (mixedFiniteCreation q n l m (quantumOccupationBasis (K:=ℝ) l x ⊗ₜ[ℝ] quantumOccupationBasis (K:=ℝ) m y))=0 := by
  rw [mixedFiniteCreation_basis,map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  simp only [map_smul,twoVertexTensorProjection,TensorProduct.map_tmul]
  rw [twoVertexProjection_basis_outside n hn (m+1) (shiftedOccupation n m 1 j y)
    (shiftedOccupation_outside_twoVertex n hn m 1 y hy j),TensorProduct.tmul_zero,smul_zero]

def mixedTwoVertexCompressedCreation (q : ℝ) (n : ℕ) (hn : 0<n) (l m : ℕ) :
    (finiteWeightSpace (K:=ℝ) l ⊗[ℝ] finiteWeightSpace (K:=ℝ) m) →ₗ[ℝ]
      (finiteWeightSpace (K:=ℝ) (l+1) ⊗[ℝ] finiteWeightSpace (K:=ℝ) (m+1)) :=
  (twoVertexTensorProjection n hn (l+1) (m+1)).comp
    ((mixedFiniteCreation q n l m).comp (twoVertexTensorEmbedding n hn l m))

/-- Exact no-return compression of the ACTUAL arbitrary-rank cup creation
on its entire physical pair space, not just on embedded boundary inputs. -/
theorem mixedFiniteCreation_boundary_compression (q : ℝ) (n : ℕ) (hn : 0<n) (l m : ℕ)
    (v : quantumOccupationSpace ℝ (Fin (n+1)) l ⊗[ℝ] quantumOccupationSpace ℝ (Fin (n+1)) m) :
    twoVertexTensorProjection n hn (l+1) (m+1) (mixedFiniteCreation q n l m v)=
      mixedTwoVertexCompressedCreation q n hn l m (twoVertexTensorProjection n hn l m v) := by
  classical
  have he : (twoVertexTensorProjection n hn (l+1) (m+1)).comp (mixedFiniteCreation q n l m)=
      (mixedTwoVertexCompressedCreation q n hn l m).comp (twoVertexTensorProjection n hn l m) := by
    apply ((quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) l).tensorProduct
      (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) m)).ext
    rintro ⟨x,y⟩
    simp only [LinearMap.comp_apply,Module.Basis.tensorProduct_apply']
    by_cases hx:∃ k : Fin (l+1),x=twoVertexOccupation n hn l k
    · rcases hx with ⟨i,rfl⟩
      by_cases hy:∃ k : Fin (m+1),y=twoVertexOccupation n hn m k
      · rcases hy with ⟨j,rfl⟩
        simp only [mixedTwoVertexCompressedCreation,LinearMap.comp_apply,twoVertexTensorProjection,
          TensorProduct.map_tmul,twoVertexProjection_basis_boundary,twoVertexTensorEmbedding,twoVertexEmbedding_basis]
      · rw [mixedFiniteCreation_projection_right_outside q n hn l m _ y hy]
        simp only [twoVertexTensorProjection,TensorProduct.map_tmul,twoVertexProjection_basis_outside n hn m y hy,
          TensorProduct.tmul_zero,map_zero]
    · rw [mixedFiniteCreation_projection_left_outside q n hn l m x y hx]
      simp only [twoVertexTensorProjection,TensorProduct.map_tmul,twoVertexProjection_basis_outside n hn l x hx,
        TensorProduct.zero_tmul,map_zero]
  exact DFunLike.congr_fun he v

end AMSPhysical
#print axioms AMSPhysical.mixedFiniteCreation_boundary_compression
