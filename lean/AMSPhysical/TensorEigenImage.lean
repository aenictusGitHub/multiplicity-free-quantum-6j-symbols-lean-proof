import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Data.Real.Basic

set_option autoImplicit false
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {V W X Y : Type*}
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

theorem tensorEigenImage_left (T : V →ₗ[ℝ] X) (S : W →ₗ[ℝ] Y) (A : Module.End ℝ X) (lam : ℝ)
    (hT : ∀ v,A (T v)=lam • T v) (p : V ⊗[ℝ] W) :
    TensorProduct.map A (LinearMap.id : Module.End ℝ Y) (TensorProduct.map T S p)=lam • TensorProduct.map T S p := by
  induction p using TensorProduct.induction_on with
  | zero => simp only [map_zero,smul_zero]
  | tmul v w => simp only [TensorProduct.map_tmul,LinearMap.id_apply,hT,TensorProduct.smul_tmul']
  | add v w hv hw => simp only [map_add,hv,hw,smul_add]

theorem tensorEigenImage_right (T : V →ₗ[ℝ] X) (S : W →ₗ[ℝ] Y) (A : Module.End ℝ Y) (lam : ℝ)
    (hS : ∀ w,A (S w)=lam • S w) (p : V ⊗[ℝ] W) :
    TensorProduct.map (LinearMap.id : Module.End ℝ X) A (TensorProduct.map T S p)=lam • TensorProduct.map T S p := by
  induction p using TensorProduct.induction_on with
  | zero => simp only [map_zero,smul_zero]
  | tmul v w => simp only [TensorProduct.map_tmul,LinearMap.id_apply,hS,TensorProduct.tmul_smul]
  | add v w hv hw => simp only [map_add,hv,hw,smul_add]

end AMSPhysical
#print axioms AMSPhysical.tensorEigenImage_left
