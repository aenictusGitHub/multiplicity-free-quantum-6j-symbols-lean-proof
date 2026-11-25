import TensorRightEigenchannel

set_option autoImplicit false
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {V W V' W':Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup V'] [Module ℝ V'] [AddCommGroup W'] [Module ℝ W']

theorem tensorRight_map_mem_range (G:V →ₗ[ℝ] V') (F:W →ₗ[ℝ] W') (S:Submodule ℝ W')
    (hF:∀ v,F v∈S) (v:V ⊗[ℝ] W):
    TensorProduct.map G F v∈LinearMap.range (TensorProduct.map (LinearMap.id:Module.End ℝ V') S.subtype) := by
  refine ⟨TensorProduct.map G (F.codRestrict S hF) v,?_⟩
  induction v using TensorProduct.induction_on with
  | zero=>simp
  | add v w hv hw=>simp only [map_add,hv,hw]
  | tmul x y=>rfl

end AMSPhysical
#print axioms AMSPhysical.tensorRight_map_mem_range
