import ActualVertexTransport
import TensorWeightedHilbert
import QuantumMixedMetric
import QuantumReverseMixedTensor
import QuantumSymmetricMetric

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {I J V W : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

theorem tensorWeightedBilin_eq_intrinsic (a : Module.Basis I ℝ V) (b : Module.Basis J ℝ W)
    (wa : I → ℝ) (wb : J → ℝ) :
    tensorWeightedBilin a b wa wb = LinearMap.BilinForm.tmul
      (finiteWeightedBilin wa a.equivFun.toLinearMap) (finiteWeightedBilin wb b.equivFun.toLinearMap) := by
  apply TensorProduct.ext'
  intro v w
  apply TensorProduct.ext'
  intro v' w'
  rw [tensorWeightedBilin_tmul]
  change _ = finiteWeightedPair wb b.equivFun.toLinearMap w w' *
    finiteWeightedPair wa a.equivFun.toLinearMap v v'
  exact mul_comm _ _

theorem symmetricTensorBilin_eq_intrinsic (q : ℝ) (n l m : ℕ) :
    symmetricTensorBilin q n l m=LinearMap.BilinForm.tmul
      (occupationCompactBilin q n l) (occupationCompactBilin q n m) :=
  tensorWeightedBilin_eq_intrinsic _ _ _ _

theorem mixedTensorBilin_eq_intrinsic (q : ℝ) (n l m : ℕ) :
    mixedTensorBilin q n l m=LinearMap.BilinForm.tmul
      (occupationCompactBilin q n l) (occupationOppositeBilin q n m) :=
  tensorWeightedBilin_eq_intrinsic _ _ _ _

theorem reverseMixedTensorBilin_eq_intrinsic (q : ℝ) (n l m : ℕ) :
    reverseMixedTensorBilin q n l m=LinearMap.BilinForm.tmul
      (occupationOppositeBilin q n l) (occupationCompactBilin q n m) :=
  tensorWeightedBilin_eq_intrinsic _ _ _ _

end AMSPhysical
#print axioms AMSPhysical.tensorWeightedBilin_eq_intrinsic
