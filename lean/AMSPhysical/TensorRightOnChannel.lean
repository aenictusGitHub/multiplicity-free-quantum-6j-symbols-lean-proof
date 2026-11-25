import TensorSubmoduleTransport

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {A V W Z : Type*} [AddCommGroup A] [Module ℝ A]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup Z] [Module ℝ Z]

theorem tensorRight_range_congr (S T : Submodule ℝ V) (h : S=T) :
    LinearMap.range (TensorProduct.map (LinearMap.id : A →ₗ[ℝ] A) S.subtype) =
      LinearMap.range (TensorProduct.map (LinearMap.id : A →ₗ[ℝ] A) T.subtype) := by
  subst T
  rfl

theorem tensorRight_equal_on_channel (S : Submodule ℝ V) (F G : V →ₗ[ℝ] W) (a : ℝ)
    (h : ∀ x∈S,F x=a • G x) (v : A ⊗[ℝ] V)
    (hv : v∈LinearMap.range (TensorProduct.map (LinearMap.id : A →ₗ[ℝ] A) S.subtype)) :
    TensorProduct.map (LinearMap.id : A →ₗ[ℝ] A) F v =
      a • TensorProduct.map (LinearMap.id : A →ₗ[ℝ] A) G v := by
  obtain ⟨u,hu⟩:=hv
  rw [← hu]
  clear hu
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u w hu hw => simp only [map_add,hu,hw,smul_add]
  | tmul x y =>
    simp only [TensorProduct.map_tmul,LinearMap.id_apply,Submodule.subtype_apply,
      h y.val y.property,TensorProduct.tmul_smul]

theorem tensorRight_map_comp (F : V →ₗ[ℝ] W) (G : W →ₗ[ℝ] Z) (v : A ⊗[ℝ] V) :
    TensorProduct.map (LinearMap.id : A →ₗ[ℝ] A) G
      (TensorProduct.map (LinearMap.id : A →ₗ[ℝ] A) F v) =
      TensorProduct.map (LinearMap.id : A →ₗ[ℝ] A) (G.comp F) v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw => simp only [map_add,hv,hw]
  | tmul x y => rfl

theorem tensorRight_identity_on_channel (S : Submodule ℝ V) (F : V →ₗ[ℝ] V)
    (h : ∀ x∈S,F x=x) (v : A ⊗[ℝ] V)
    (hv : v∈LinearMap.range (TensorProduct.map (LinearMap.id : A →ₗ[ℝ] A) S.subtype)) :
    TensorProduct.map (LinearMap.id : A →ₗ[ℝ] A) F v=v := by
  obtain ⟨u,hu⟩:=hv
  rw [← hu]
  clear hu
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u w hu hw => simp only [map_add,hu,hw]
  | tmul x y => simp only [TensorProduct.map_tmul,LinearMap.id_apply,Submodule.subtype_apply,h y.val y.property]

end AMSPhysical
#print axioms AMSPhysical.tensorRight_equal_on_channel
