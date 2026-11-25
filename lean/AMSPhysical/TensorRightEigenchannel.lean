import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.TensorProduct.Submodule

set_option autoImplicit false
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {V W:Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

theorem tensorRight_eigen_on_range (A:Module.End ℝ W) (S:Submodule ℝ W) (ev:ℝ)
    (hA:∀ v∈S,A v=ev • v) (v:V ⊗[ℝ] W)
    (hv:v∈LinearMap.range (TensorProduct.map (LinearMap.id:Module.End ℝ V) S.subtype)):
    TensorProduct.map (LinearMap.id:Module.End ℝ V) A v=ev • v := by
  obtain ⟨w,rfl⟩:=hv
  induction w using TensorProduct.induction_on with
  | zero=>simp
  | add w z hw hz=>simp only [map_add,hw,hz,smul_add]
  | tmul x y=>
    simp only [TensorProduct.map_tmul,LinearMap.id_apply,Submodule.subtype_apply]
    rw [hA y.val y.property,TensorProduct.tmul_smul]

end AMSPhysical
#print axioms AMSPhysical.tensorRight_eigen_on_range
