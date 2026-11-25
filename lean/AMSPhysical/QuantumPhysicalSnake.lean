import QuantumReverseEvaluation
import QuantumSymmetricDualAdjoint
import DiagonalSnake

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem signed_duality_coefficient (s w : ℝ) (hw : w≠0) (hs : s*s=1) : (s/w)*(s*w)=1 := by
  have he : (s/w)*(s*w)=s*s := by field_simp [hw]
  exact he.trans hs

theorem symmetricPhysicalEvaluation_eq_diagonal (q : ℝ) (n L : ℕ) :
    symmetricPhysicalEvaluation q n L=diagonalEvaluation (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L)
      (fun x =>occupationDualSign n L x*occupationOppositeWeight q n L x) := by
  apply LinearMap.ext
  intro v
  exact (symmetricPhysicalEvaluation_diagonal q n L v).symm

section Snakes
variable (q : ℝ) (hq : 0<q) (n L : ℕ)
include hq
local notation "V" => quantumOccupationSpace ℝ (Fin (n+1)) L
local notation "b" => quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L

/-- Physical right duality snake for the symmetric representation. -/
theorem symmetric_physical_snake_right (v : V) :
    (TensorProduct.lid ℝ V)
      (TensorProduct.map (symmetricPhysicalEvaluation q n L) (LinearMap.id : V →ₗ[ℝ] V)
        ((TensorProduct.assoc ℝ V V V).symm (v ⊗ₜ[ℝ] symmetricReverseCoevaluation q n L)))=v := by
  rw [symmetricPhysicalEvaluation_eq_diagonal]
  apply diagonal_snake_right
  intro x
  exact signed_duality_coefficient _ _ (ne_of_gt (occupationOppositeWeight_pos q hq n L x))
    (occupationDualSign_square n L x)

/-- Physical left duality snake for the symmetric representation. -/
theorem symmetric_physical_snake_left (v : V) :
    (TensorProduct.rid ℝ V)
      (TensorProduct.map (LinearMap.id : V →ₗ[ℝ] V) (symmetricReverseEvaluation q n L)
        ((TensorProduct.assoc ℝ V V V) (symmetricCoevaluation q n L ⊗ₜ[ℝ] v)))=v := by
  rw [symmetricCoevaluation_diagonal]
  apply diagonal_snake_left
  intro x
  exact signed_duality_coefficient _ _ (ne_of_gt (occupationCompactWeight_pos q hq n L x))
    (occupationDualSign_square n L x)

/-- The other right snake, for the opposite symmetric representation. -/
theorem opposite_physical_snake_right (v : V) :
    (TensorProduct.lid ℝ V)
      (TensorProduct.map (symmetricReverseEvaluation q n L) (LinearMap.id : V →ₗ[ℝ] V)
        ((TensorProduct.assoc ℝ V V V).symm (v ⊗ₜ[ℝ] symmetricCoevaluation q n L)))=v := by
  rw [symmetricCoevaluation_diagonal]
  apply diagonal_snake_right
  intro x
  exact signed_duality_coefficient _ _ (ne_of_gt (occupationCompactWeight_pos q hq n L x))
    (occupationDualSign_square n L x)

/-- The other left snake, for the opposite symmetric representation. -/
theorem opposite_physical_snake_left (v : V) :
    (TensorProduct.rid ℝ V)
      (TensorProduct.map (LinearMap.id : V →ₗ[ℝ] V) (symmetricPhysicalEvaluation q n L)
        ((TensorProduct.assoc ℝ V V V) (symmetricReverseCoevaluation q n L ⊗ₜ[ℝ] v)))=v := by
  rw [symmetricPhysicalEvaluation_eq_diagonal]
  apply diagonal_snake_left
  intro x
  exact signed_duality_coefficient _ _ (ne_of_gt (occupationOppositeWeight_pos q hq n L x))
    (occupationDualSign_square n L x)

end Snakes
end AMSPhysical
#print axioms AMSPhysical.symmetric_physical_snake_right
