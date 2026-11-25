import TensorWeightedIsometries

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {ι κ V U : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup U] [Module ℝ U]

theorem tensorWeightedBilin_submodule_orthogonal
    (b : Module.Basis ι ℝ V) (c : Module.Basis κ ℝ U) (w : ι → ℝ) (z : κ → ℝ)
    (S T : Submodule ℝ V)
    (hST : ∀ x∈S,∀ y∈T,finiteWeightedPair w b.equivFun.toLinearMap x y=0)
    (x : S ⊗[ℝ] U) (y : T ⊗[ℝ] U) :
    tensorWeightedBilin b c w z
      (TensorProduct.map S.subtype (LinearMap.id : Module.End ℝ U) x)
      (TensorProduct.map T.subtype (LinearMap.id : Module.End ℝ U) y)=0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add,LinearMap.add_apply,hx,hx',add_zero]
  | tmul v u =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add,hy,hy',add_zero]
    | tmul v' u' =>
      simp only [TensorProduct.map_tmul,LinearMap.id_apply,Submodule.subtype_apply,tensorWeightedBilin_tmul]
      rw [hST v.val v.property v'.val v'.property,zero_mul]

end AMSPhysical
#print axioms AMSPhysical.tensorWeightedBilin_submodule_orthogonal
