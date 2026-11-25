import TensorBasisSlices
import FiniteRightBending

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {V W U I J K:Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [AddCommGroup U] [Module ℝ U]

theorem tensor_assoc_coordinate (b:Module.Basis I ℝ V) (c:Module.Basis J ℝ W) (d:Module.Basis K ℝ U)
    (w:(V ⊗[ℝ] W) ⊗[ℝ] U) (i:I) (j:J) (k:K) :
    (b.tensorProduct (c.tensorProduct d)).repr ((TensorProduct.assoc ℝ V W U) w) (i,(j,k))=
      ((b.tensorProduct c).tensorProduct d).repr w ((i,j),k) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w z hw hz => simp only [map_add,Finsupp.add_apply,hw,hz]
  | tmul u v =>
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add u u' hu hu' => simp only [TensorProduct.add_tmul,map_add,Finsupp.add_apply,hu,hu']
    | tmul x y =>
      simp only [TensorProduct.assoc_tmul,Module.Basis.tensorProduct_repr_tmul_apply,smul_eq_mul]
      ring

variable {X:Type*} [AddCommGroup X] [Module ℝ X] [Fintype J] [DecidableEq J]

theorem bendRight_diagonal_coordinate (b:Module.Basis I ℝ V) (c:Module.Basis J ℝ W)
    (d:J → ℝ) (T:X ⊗[ℝ] W →ₗ[ℝ] V) (x:X) (i:I) (j:J) :
    (b.tensorProduct c).repr (bendRight T (diagonalCoevaluation c d) x) (i,j)=
      d j*b.repr (T (x ⊗ₜ[ℝ] c j)) i := by
  rw [bendRight_diagonal]
  exact tensor_sum_right_coefficient b c (fun j=>j) Function.injective_id d (fun j=>T (x ⊗ₜ[ℝ] c j)) i j

end AMSPhysical
#print axioms AMSPhysical.tensor_assoc_coordinate
#print axioms AMSPhysical.bendRight_diagonal_coordinate
