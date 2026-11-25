import GlobalTensorChannelMetric

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {I J K V W Z H : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup Z] [Module ℝ Z] [AddCommGroup H] [Module ℝ H]

theorem tensorWeightedBilin_right_carrier_scale
    (a : Module.Basis I ℝ V) (b : Module.Basis J ℝ W) (c : Module.Basis K ℝ Z)
    (wa : I → ℝ) (wb : J → ℝ) (wc : K → ℝ)
    (F : H →ₗ[ℝ] W) (G : H →ₗ[ℝ] Z) (s : ℝ)
    (hFG : ∀ x y,finiteWeightedPair wc c.equivFun.toLinearMap (G x) (G y) =
      s*finiteWeightedPair wb b.equivFun.toLinearMap (F x) (F y)) (u v : V ⊗[ℝ] H) :
    tensorWeightedBilin a c wa wc (TensorProduct.map LinearMap.id G u) (TensorProduct.map LinearMap.id G v) =
      s*tensorWeightedBilin a b wa wb (TensorProduct.map LinearMap.id F u) (TensorProduct.map LinearMap.id F v) := by
  induction u using TensorProduct.induction_on with
  | zero => simp only [map_zero,LinearMap.zero_apply,mul_zero]
  | add u w hu hw => simp only [map_add,LinearMap.add_apply,hu,hw,mul_add]
  | tmul x h =>
    induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero,mul_zero]
    | add v w hv hw => simp only [map_add,hv,hw,mul_add]
    | tmul y k =>
      simp only [TensorProduct.map_tmul,LinearMap.id_apply,tensorWeightedBilin_tmul,hFG]
      ring

theorem tensorWeightedBilin_left_carrier_scale
    (a : Module.Basis I ℝ V) (b : Module.Basis J ℝ W) (c : Module.Basis K ℝ Z)
    (wa : I → ℝ) (wb : J → ℝ) (wc : K → ℝ)
    (F : H →ₗ[ℝ] V) (G : H →ₗ[ℝ] Z) (s : ℝ)
    (hFG : ∀ x y,finiteWeightedPair wc c.equivFun.toLinearMap (G x) (G y) =
      s*finiteWeightedPair wa a.equivFun.toLinearMap (F x) (F y)) (u v : H ⊗[ℝ] W) :
    tensorWeightedBilin c b wc wb (TensorProduct.map G LinearMap.id u) (TensorProduct.map G LinearMap.id v) =
      s*tensorWeightedBilin a b wa wb (TensorProduct.map F LinearMap.id u) (TensorProduct.map F LinearMap.id v) := by
  induction u using TensorProduct.induction_on with
  | zero => simp only [map_zero,LinearMap.zero_apply,mul_zero]
  | add u w hu hw => simp only [map_add,LinearMap.add_apply,hu,hw,mul_add]
  | tmul h x =>
    induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero,mul_zero]
    | add v w hv hw => simp only [map_add,hv,hw,mul_add]
    | tmul k y =>
      simp only [TensorProduct.map_tmul,LinearMap.id_apply,tensorWeightedBilin_tmul,hFG]
      ring

end AMSPhysical
#print axioms AMSPhysical.tensorWeightedBilin_right_carrier_scale
