import TensorWeightedIsometries

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {V W U : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup U] [Module ℝ U]

/-- An actual module equivalence carrying a pair channel onto another
also carries the corresponding physical triple tensor images exactly. -/
theorem tensorRightChannel_equiv_map (e : V ≃ₗ[ℝ] W) (S : Submodule ℝ V) (T : Submodule ℝ W)
    (he : S.map e.toLinearMap=T) :
    (LinearMap.range (TensorProduct.map (LinearMap.id : Module.End ℝ U) S.subtype)).map
      (TensorProduct.congr (LinearEquiv.refl ℝ U) e).toLinearMap=
    LinearMap.range (TensorProduct.map (LinearMap.id : Module.End ℝ U) T.subtype) := by
  let eS : S ≃ₗ[ℝ] T:=e.ofSubmodules S T he
  let E : U ⊗[ℝ] V ≃ₗ[ℝ] U ⊗[ℝ] W:=TensorProduct.congr (LinearEquiv.refl ℝ U) e
  let ES : U ⊗[ℝ] S ≃ₗ[ℝ] U ⊗[ℝ] T:=TensorProduct.congr (LinearEquiv.refl ℝ U) eS
  have hsquare : E.toLinearMap.comp (TensorProduct.map (LinearMap.id : Module.End ℝ U) S.subtype)=
      (TensorProduct.map (LinearMap.id : Module.End ℝ U) T.subtype).comp ES.toLinearMap := by
    apply TensorProduct.ext'
    intro u s
    rfl
  ext w
  constructor
  · rintro ⟨v,⟨x,rfl⟩,rfl⟩
    refine ⟨ES x,?_⟩
    exact (DFunLike.congr_fun hsquare x).symm
  · rintro ⟨y,rfl⟩
    refine ⟨TensorProduct.map (LinearMap.id : Module.End ℝ U) S.subtype (ES.symm y),⟨ES.symm y,rfl⟩,?_⟩
    change E (TensorProduct.map _ _ (ES.symm y))=_
    have hh:=DFunLike.congr_fun hsquare (ES.symm y)
    simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply] using hh

end AMSPhysical
#print axioms AMSPhysical.tensorRightChannel_equiv_map
