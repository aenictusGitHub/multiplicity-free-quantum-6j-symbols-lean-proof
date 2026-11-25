import TensorWeightedIsometries

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct
variable {ι κ V W U X V' W' : Type*}
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup V'] [Module ℝ V'] [AddCommGroup W'] [Module ℝ W']

theorem tensorWeightedBilin_map_zero (b : Basis ι ℝ V') (c : Basis κ ℝ W')
    (w : ι → ℝ) (z : κ → ℝ) (A : V →ₗ[ℝ] V') (S : U →ₗ[ℝ] V')
    (D : W →ₗ[ℝ] W') (E : X →ₗ[ℝ] W')
    (h : ∀ p p' v v',finiteWeightedPair w b.equivFun.toLinearMap (A p) (S p')*
      finiteWeightedPair z c.equivFun.toLinearMap (D v) (E v')=0)
    (p : V ⊗[ℝ] W) (v : U ⊗[ℝ] X) :
    tensorWeightedBilin b c w z (TensorProduct.map A D p) (TensorProduct.map S E v)=0 := by
  have he : ((tensorWeightedBilin b c w z).comp (TensorProduct.map A D)).compl₂
      (TensorProduct.map S E)=0 := by
    apply TensorProduct.ext'
    intro a d
    apply TensorProduct.ext'
    intro s e
    change tensorWeightedBilin b c w z (TensorProduct.map A D (a ⊗ₜ[ℝ] d))
      (TensorProduct.map S E (s ⊗ₜ[ℝ] e))=0
    rw [TensorProduct.map_tmul,TensorProduct.map_tmul,tensorWeightedBilin_tmul]
    exact h a s d e
  exact DFunLike.congr_fun (DFunLike.congr_fun he p) v

end AMSPhysical

#print axioms AMSPhysical.tensorWeightedBilin_map_zero
