import DiagonalCoevaluation
import Mathlib.LinearAlgebra.TensorProduct.Associator

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {V I : Type*} [AddCommGroup V] [Module ℝ V] [Fintype I] [DecidableEq I]

theorem diagonalEvaluation_basis_right (b : Module.Basis I ℝ V) (d : I → ℝ) (v : V) (i : I) :
    diagonalEvaluation b d (v ⊗ₜ[ℝ] b i)=d i*b.equivFun v i := by
  change finiteWeightedPair d b.equivFun.toLinearMap v (b i)=_
  exact finiteWeightedPair_basis_right b d v i

theorem diagonalEvaluation_basis_left (b : Module.Basis I ℝ V) (d : I → ℝ) (v : V) (i : I) :
    diagonalEvaluation b d (b i ⊗ₜ[ℝ] v)=d i*b.equivFun v i := by
  change finiteWeightedPair d b.equivFun.toLinearMap (b i) v=_
  rw [finiteWeightedPair_symm]
  exact finiteWeightedPair_basis_right b d v i

/-- A literal right snake identity, with actual tensor associator, evaluation,
coevaluation and unit map, rather than an abstract rigidity assumption. -/
theorem diagonal_snake_right (b : Module.Basis I ℝ V) (c d : I → ℝ)
    (hcd : ∀ i,c i*d i=1) (v : V) :
    (TensorProduct.lid ℝ V)
      (TensorProduct.map (diagonalEvaluation b d) (LinearMap.id : V →ₗ[ℝ] V)
        ((TensorProduct.assoc ℝ V V V).symm (v ⊗ₜ[ℝ] diagonalCoevaluation b c)))=v := by
  simp only [diagonalCoevaluation,TensorProduct.tmul_sum,TensorProduct.tmul_smul,
    map_sum,map_smul,TensorProduct.assoc_symm_tmul,TensorProduct.map_tmul,LinearMap.id_apply,
    TensorProduct.lid_tmul,diagonalEvaluation_basis_right,smul_smul]
  calc
    _ = ∑ i,b.equivFun v i • b i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← mul_assoc,hcd,one_mul]
    _ = v := b.sum_repr v

/-- The literal left snake identity in the other tensor bracketing. -/
theorem diagonal_snake_left (b : Module.Basis I ℝ V) (c d : I → ℝ)
    (hcd : ∀ i,c i*d i=1) (v : V) :
    (TensorProduct.rid ℝ V)
      (TensorProduct.map (LinearMap.id : V →ₗ[ℝ] V) (diagonalEvaluation b d)
        ((TensorProduct.assoc ℝ V V V) (diagonalCoevaluation b c ⊗ₜ[ℝ] v)))=v := by
  simp only [diagonalCoevaluation,TensorProduct.sum_tmul,← TensorProduct.smul_tmul',
    map_sum,map_smul,TensorProduct.assoc_tmul,TensorProduct.map_tmul,LinearMap.id_apply,
    TensorProduct.rid_tmul,diagonalEvaluation_basis_left,smul_smul]
  calc
    _ = ∑ i,b.equivFun v i • b i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← mul_assoc,hcd,one_mul]
    _ = v := b.sum_repr v

end AMSPhysical
