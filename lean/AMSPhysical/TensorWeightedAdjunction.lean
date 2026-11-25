import TensorWeightedHilbert

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct
variable {I J H V W U : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W] [AddCommGroup U] [Module ℝ U]

theorem tensorWeightedAdjunction_right (b : Basis I ℝ V) (c : Basis J ℝ W) (d : Basis H ℝ U)
    (a : I → ℝ) (w : J → ℝ) (u : H → ℝ) (T : W →ₗ[ℝ] U) (D : U →ₗ[ℝ] W)
    (hTD : ∀ v z,finiteWeightedPair u d.equivFun.toLinearMap (T v) z=
      finiteWeightedPair w c.equivFun.toLinearMap v (D z)) (v : V ⊗[ℝ] W) (z : V ⊗[ℝ] U) :
    tensorWeightedBilin b d a u (TensorProduct.map LinearMap.id T v) z=
      tensorWeightedBilin b c a w v (TensorProduct.map LinearMap.id D z) := by
  have he : (tensorWeightedBilin b d a u).comp (TensorProduct.map LinearMap.id T)=
      (tensorWeightedBilin b c a w).compl₂ (TensorProduct.map LinearMap.id D) := by
    apply (b.tensorProduct c).ext
    intro ij
    apply (b.tensorProduct d).ext
    intro kh
    change tensorWeightedBilin b d a u (TensorProduct.map LinearMap.id T ((b.tensorProduct c) ij)) ((b.tensorProduct d) kh)=
      tensorWeightedBilin b c a w ((b.tensorProduct c) ij) (TensorProduct.map LinearMap.id D ((b.tensorProduct d) kh))
    rw [Basis.tensorProduct_apply',Basis.tensorProduct_apply',TensorProduct.map_tmul,TensorProduct.map_tmul,
      LinearMap.id_apply,LinearMap.id_apply,tensorWeightedBilin_tmul,tensorWeightedBilin_tmul,hTD]
  exact DFunLike.congr_fun (DFunLike.congr_fun he v) z

theorem tensorWeightedAdjunction_left (b : Basis I ℝ V) (c : Basis J ℝ W) (d : Basis H ℝ U)
    (a : I → ℝ) (w : J → ℝ) (u : H → ℝ) (T : V →ₗ[ℝ] U) (D : U →ₗ[ℝ] V)
    (hTD : ∀ v z,finiteWeightedPair u d.equivFun.toLinearMap (T v) z=
      finiteWeightedPair a b.equivFun.toLinearMap v (D z)) (v : V ⊗[ℝ] W) (z : U ⊗[ℝ] W) :
    tensorWeightedBilin d c u w (TensorProduct.map T LinearMap.id v) z=
      tensorWeightedBilin b c a w v (TensorProduct.map D LinearMap.id z) := by
  have he : (tensorWeightedBilin d c u w).comp (TensorProduct.map T LinearMap.id)=
      (tensorWeightedBilin b c a w).compl₂ (TensorProduct.map D LinearMap.id) := by
    apply (b.tensorProduct c).ext
    intro ij
    apply (d.tensorProduct c).ext
    intro kh
    change tensorWeightedBilin d c u w (TensorProduct.map T LinearMap.id ((b.tensorProduct c) ij)) ((d.tensorProduct c) kh)=
      tensorWeightedBilin b c a w ((b.tensorProduct c) ij) (TensorProduct.map D LinearMap.id ((d.tensorProduct c) kh))
    rw [Basis.tensorProduct_apply',Basis.tensorProduct_apply',TensorProduct.map_tmul,TensorProduct.map_tmul,
      LinearMap.id_apply,LinearMap.id_apply,tensorWeightedBilin_tmul,tensorWeightedBilin_tmul,hTD]
  exact DFunLike.congr_fun (DFunLike.congr_fun he v) z

end AMSPhysical
#print axioms AMSPhysical.tensorWeightedAdjunction_right
#print axioms AMSPhysical.tensorWeightedAdjunction_left
