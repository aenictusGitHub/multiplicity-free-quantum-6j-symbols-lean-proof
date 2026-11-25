import TensorBasisSlices
import TensorWeightedHilbert
import FiniteWeightedDuality

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {V I : Type*} [AddCommGroup V] [Module ℝ V] [Fintype I] [DecidableEq I]

def diagonalCoevaluation (b : Module.Basis I ℝ V) (c : I → ℝ) : V ⊗[ℝ] V :=
  ∑ i,c i • (b i ⊗ₜ[ℝ] b i)

def diagonalEvaluation (b : Module.Basis I ℝ V) (d : I → ℝ) : (V ⊗[ℝ] V) →ₗ[ℝ] ℝ :=
  TensorProduct.lift (finiteWeightedBilin d b.equivFun.toLinearMap)

theorem diagonalEvaluation_smul (b : Module.Basis I ℝ V) (d : I → ℝ) (a : ℝ) (v : V ⊗[ℝ] V) :
    diagonalEvaluation b (fun i =>a*d i) v=a*diagonalEvaluation b d v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul v w =>
    change (∑ i,(a*d i)*b.equivFun v i*b.equivFun w i)=a*(∑ i,d i*b.equivFun v i*b.equivFun w i)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  | add v w hv hw => simp only [map_add,hv,hw,mul_add]

theorem diagonalCoevaluation_coordinate (b : Module.Basis I ℝ V) (c : I → ℝ) (i j : I) :
    (b.tensorProduct b).repr (diagonalCoevaluation b c) (i,j)=c i*(if i=j then 1 else 0) := by
  have h:=tensor_sum_left_coefficient b b (fun k : I =>k) Function.injective_id c (fun k =>b k) i j
  rw [Module.Basis.repr_self] at h
  simp only [← TensorProduct.smul_tmul',Finsupp.single_apply] at h
  exact h

/-- The coevaluation tensor is the actual compact adjoint of its
evaluation functional exactly when the displayed diagonal weights match. -/
theorem diagonalCoevaluation_adjoint (b : Module.Basis I ℝ V) (w z c d : I → ℝ)
    (hWeight : ∀ i,c i*w i*z i=d i) (v : V ⊗[ℝ] V) :
    tensorWeightedBilin b b w z (diagonalCoevaluation b c) v=diagonalEvaluation b d v := by
  have hMaps : tensorWeightedBilin b b w z (diagonalCoevaluation b c)=diagonalEvaluation b d := by
    apply (b.tensorProduct b).ext
    intro p
    change finiteWeightedPair (fun ij : I × I =>w ij.1*z ij.2)
      (b.tensorProduct b).equivFun.toLinearMap (diagonalCoevaluation b c) ((b.tensorProduct b) p)=_
    rw [finiteWeightedPair_basis_right]
    conv_rhs => rw [Module.Basis.tensorProduct_apply']
    change (w p.1*z p.2)*(b.tensorProduct b).repr (diagonalCoevaluation b c) p=
      finiteWeightedPair d b.equivFun.toLinearMap (b p.1) (b p.2)
    rw [diagonalCoevaluation_coordinate,finiteWeightedPair_basis]
    rcases p with ⟨i,j⟩
    dsimp only
    by_cases hij : i=j
    · subst j
      rw [if_pos rfl,if_pos rfl]
      linear_combination hWeight i
    · rw [if_neg hij,if_neg hij,mul_zero,mul_zero]
  exact DFunLike.congr_fun hMaps v

end AMSPhysical
