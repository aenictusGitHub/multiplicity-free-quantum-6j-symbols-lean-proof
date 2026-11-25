import Mathlib.RingTheory.Flat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Eigenspace.Basic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

theorem tensorEigenspace_left (A : Module.End ℝ V) (lam : ℝ) :
    Module.End.eigenspace (R:=ℝ) (M:=V ⊗[ℝ] W) (TensorProduct.map A (LinearMap.id : Module.End ℝ W)) lam=
      LinearMap.range (TensorProduct.map (A.eigenspace lam).subtype (LinearMap.id : Module.End ℝ W)) := by
  have ht:=Module.Flat.rTensor_exact W (LinearMap.exact_subtype_ker_map (A-lam • LinearMap.id))
  have he : (A-lam • LinearMap.id).rTensor W=
      TensorProduct.map A (LinearMap.id : Module.End ℝ W)-lam • LinearMap.id := by
    rw [LinearMap.rTensor_sub,LinearMap.rTensor_smul,LinearMap.rTensor_id]
    rfl
  have hsub : A.eigenspace lam=LinearMap.ker (A-lam • LinearMap.id) := by
    rw [Module.End.eigenspace_def,Module.End.one_eq_id]
  rw [hsub,Module.End.eigenspace_def]
  change LinearMap.ker (TensorProduct.map A (LinearMap.id : Module.End ℝ W)-lam • LinearMap.id)=_
  rw [← he]
  exact ht.linearMap_ker_eq

theorem tensorEigenspace_right (A : Module.End ℝ W) (lam : ℝ) :
    Module.End.eigenspace (R:=ℝ) (M:=V ⊗[ℝ] W) (TensorProduct.map (LinearMap.id : Module.End ℝ V) A) lam=
      LinearMap.range (TensorProduct.map (LinearMap.id : Module.End ℝ V) (A.eigenspace lam).subtype) := by
  have ht:=Module.Flat.lTensor_exact V (LinearMap.exact_subtype_ker_map (A-lam • LinearMap.id))
  have he : (A-lam • LinearMap.id).lTensor V=
      TensorProduct.map (LinearMap.id : Module.End ℝ V) A-lam • LinearMap.id := by
    rw [LinearMap.lTensor_sub,LinearMap.lTensor_smul,LinearMap.lTensor_id]
    rfl
  have hsub : A.eigenspace lam=LinearMap.ker (A-lam • LinearMap.id) := by
    rw [Module.End.eigenspace_def,Module.End.one_eq_id]
  rw [hsub,Module.End.eigenspace_def]
  change LinearMap.ker (TensorProduct.map (LinearMap.id : Module.End ℝ V) A-lam • LinearMap.id)=_
  rw [← he]
  exact ht.linearMap_ker_eq

end AMSPhysical
#print axioms AMSPhysical.tensorEigenspace_left
#print axioms AMSPhysical.tensorEigenspace_right
