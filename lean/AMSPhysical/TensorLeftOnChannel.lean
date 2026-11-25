import TensorRightOnChannel
import TensorChannelScaledMetric

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {A V W Z : Type*} [AddCommGroup A] [Module ℝ A]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup Z] [Module ℝ Z]

theorem tensorLeft_range_congr (S T : Submodule ℝ V) (h : S=T) :
    LinearMap.range (TensorProduct.map S.subtype (LinearMap.id : A →ₗ[ℝ] A)) =
      LinearMap.range (TensorProduct.map T.subtype (LinearMap.id : A →ₗ[ℝ] A)) := by
  subst T
  rfl

theorem tensorLeft_equal_on_channel (S : Submodule ℝ V) (F G : V →ₗ[ℝ] W) (a : ℝ)
    (h : ∀ x∈S,F x=a • G x) (v : V ⊗[ℝ] A)
    (hv : v∈LinearMap.range (TensorProduct.map S.subtype (LinearMap.id : A →ₗ[ℝ] A))) :
    TensorProduct.map F (LinearMap.id : A →ₗ[ℝ] A) v =
      a • TensorProduct.map G (LinearMap.id : A →ₗ[ℝ] A) v := by
  obtain ⟨u,hu⟩:=hv
  rw [← hu]
  clear hu
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u w hu hw => simp only [map_add,hu,hw,smul_add]
  | tmul x y =>
    simp only [TensorProduct.map_tmul,LinearMap.id_apply,Submodule.subtype_apply,
      h x.val x.property,TensorProduct.smul_tmul']

theorem tensorLeft_map_comp (F : V →ₗ[ℝ] W) (G : W →ₗ[ℝ] Z) (v : V ⊗[ℝ] A) :
    TensorProduct.map G (LinearMap.id : A →ₗ[ℝ] A)
      (TensorProduct.map F (LinearMap.id : A →ₗ[ℝ] A) v) =
      TensorProduct.map (G.comp F) (LinearMap.id : A →ₗ[ℝ] A) v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw => simp only [map_add,hv,hw]
  | tmul x y => rfl

theorem tensorLeft_identity_on_channel (S : Submodule ℝ V) (F : V →ₗ[ℝ] V)
    (h : ∀ x∈S,F x=x) (v : V ⊗[ℝ] A)
    (hv : v∈LinearMap.range (TensorProduct.map S.subtype (LinearMap.id : A →ₗ[ℝ] A))) :
    TensorProduct.map F (LinearMap.id : A →ₗ[ℝ] A) v=v := by
  obtain ⟨u,hu⟩:=hv
  rw [← hu]
  clear hu
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u w hu hw => simp only [map_add,hu,hw]
  | tmul x y => simp only [TensorProduct.map_tmul,LinearMap.id_apply,Submodule.subtype_apply,h x.val x.property]

end AMSPhysical
#print axioms AMSPhysical.tensorLeft_equal_on_channel
