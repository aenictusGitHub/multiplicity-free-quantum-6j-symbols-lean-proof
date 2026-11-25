import FiniteRightBending
import TensorWeightedHilbert

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {X V W I J : Type*} [AddCommGroup X] [Module ℝ X]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Exact finite metric formula for bending with a diagonal physical cup.
This keeps the opposite-leg metric factor explicit. -/
theorem bendRight_diagonal_metric (b:Module.Basis I ℝ V) (t:Module.Basis J ℝ W)
    (c z:I → ℝ) (w:J → ℝ) (T:X ⊗[ℝ] V →ₗ[ℝ] W) (x y:X) :
    tensorWeightedBilin t b w z (bendRight T (diagonalCoevaluation b c) x)
      (bendRight T (diagonalCoevaluation b c) y)=
      ∑ i,c i*c i*z i*finiteWeightedPair w t.equivFun.toLinearMap
        (T (x ⊗ₜ[ℝ] b i)) (T (y ⊗ₜ[ℝ] b i)) := by
  rw [bendRight_diagonal,bendRight_diagonal]
  simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,smul_eq_mul,
    tensorWeightedBilin_tmul,finiteWeightedPair_basis]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  calc
    _=∑ j,if j=i then c i*c i*z i*finiteWeightedPair w t.equivFun.toLinearMap
        (T (x ⊗ₜ[ℝ] b i)) (T (y ⊗ₜ[ℝ] b i)) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases he:j=i
      · subst j
        simp only [if_pos rfl,ite_true]
        ring
      · simp only [if_neg he,mul_zero,zero_mul]
    _=_ := by simp

end AMSPhysical
#print axioms AMSPhysical.bendRight_diagonal_metric
