import TensorWeightedBilinIntrinsic
import QuantumTripleLeftTensorMetric
import QuantumTypeIITriple

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

theorem physicalLeftTripleBilin_eq_intrinsic (q : ℝ) (n l m c : ℕ) :
    physicalLeftTripleBilin q n l m c =
      LinearMap.BilinForm.tmul (mixedTensorBilin q n l m) (occupationCompactBilin q n c) := by
  unfold physicalLeftTripleBilin
  rw [tensorWeightedBilin_eq_intrinsic]
  rfl

theorem physicalTripleBilin_eq_intrinsic_right (q : ℝ) (n a s p : ℕ) :
    physicalTripleBilin q n a s p = LinearMap.BilinForm.tmul
      (occupationCompactBilin q n a) (reverseMixedTensorBilin q n s p) := by
  rw [physicalTripleBilin_tensor]
  unfold physicalTripleTensorBilin
  rw [tensorWeightedBilin_eq_intrinsic]
  rfl

end AMSPhysical
#print axioms AMSPhysical.physicalLeftTripleBilin_eq_intrinsic
