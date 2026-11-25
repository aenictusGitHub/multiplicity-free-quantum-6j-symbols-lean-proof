import QuantumTypeABending
import DiagonalSnake

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct
variable {X V W I : Type*}
  [AddCommGroup X] [Module ℝ X] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [Fintype I] [DecidableEq I]

def unbendRight (S : X →ₗ[ℝ] W ⊗[ℝ] V) (ev : (V ⊗[ℝ] V) →ₗ[ℝ] ℝ) :
    (X ⊗[ℝ] V) →ₗ[ℝ] W :=
  (TensorProduct.rid ℝ W).toLinearMap.comp
    ((TensorProduct.map (LinearMap.id : W →ₗ[ℝ] W) ev).comp
      ((TensorProduct.assoc ℝ W V V).toLinearMap.comp
        (TensorProduct.map S (LinearMap.id : V →ₗ[ℝ] V))))

theorem bendRight_diagonal (b : Module.Basis I ℝ V) (c : I → ℝ)
    (T : (X ⊗[ℝ] V) →ₗ[ℝ] W) (x : X) :
    bendRight T (diagonalCoevaluation b c) x=
      ∑ i,c i • (T (x ⊗ₜ[ℝ] b i) ⊗ₜ[ℝ] b i) := by
  change TensorProduct.map T (LinearMap.id : V →ₗ[ℝ] V)
    ((TensorProduct.assoc ℝ X V V).symm (x ⊗ₜ[ℝ] diagonalCoevaluation b c))=_
  simp only [diagonalCoevaluation,TensorProduct.tmul_sum,TensorProduct.tmul_smul,
    map_sum,map_smul,TensorProduct.assoc_symm_tmul,TensorProduct.map_tmul,LinearMap.id_apply]

theorem unbendRight_tmul (S : X →ₗ[ℝ] W ⊗[ℝ] V)
    (ev : (V ⊗[ℝ] V) →ₗ[ℝ] ℝ) (x : X) (v : V) :
    unbendRight S ev (x ⊗ₜ[ℝ] v)=
      (TensorProduct.rid ℝ W)
        (TensorProduct.map (LinearMap.id : W →ₗ[ℝ] W) ev
          ((TensorProduct.assoc ℝ W V V) (S x ⊗ₜ[ℝ] v))) := rfl

theorem unbendRight_bendRight_diagonal (b : Module.Basis I ℝ V) (c d : I → ℝ)
    (hcd : ∀ i,c i*d i=1) (T : (X ⊗[ℝ] V) →ₗ[ℝ] W) :
    unbendRight (bendRight T (diagonalCoevaluation b c)) (diagonalEvaluation b d)=T := by
  apply TensorProduct.ext
  ext x v
  change unbendRight (bendRight T (diagonalCoevaluation b c)) (diagonalEvaluation b d) (x ⊗ₜ[ℝ] v)=_
  rw [unbendRight_tmul,bendRight_diagonal]
  simp only [TensorProduct.sum_tmul,← TensorProduct.smul_tmul',map_sum,map_smul,
    TensorProduct.assoc_tmul,TensorProduct.map_tmul,LinearMap.id_apply,
    TensorProduct.rid_tmul,diagonalEvaluation_basis_left,smul_smul]
  calc
    _ = ∑ i,b.equivFun v i • T (x ⊗ₜ[ℝ] b i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← mul_assoc,hcd,one_mul]
    _ = T (x ⊗ₜ[ℝ] v) := by
      simp_rw [← map_smul T]
      rw [← map_sum]
      conv_rhs => rw [← b.sum_repr v]
      simp only [TensorProduct.tmul_sum,TensorProduct.tmul_smul]
      rfl

theorem bendRight_unbendRight_diagonal (b : Module.Basis I ℝ V) (c d : I → ℝ)
    (hcd : ∀ i,c i*d i=1) (S : X →ₗ[ℝ] W ⊗[ℝ] V) :
    bendRight (unbendRight S (diagonalEvaluation b d)) (diagonalCoevaluation b c)=S := by
  apply LinearMap.ext
  intro x
  rw [bendRight_diagonal]
  have hs : ∀ s : W ⊗[ℝ] V,
      (∑ i,c i • ((TensorProduct.rid ℝ W)
        (TensorProduct.map (LinearMap.id : W →ₗ[ℝ] W) (diagonalEvaluation b d)
          ((TensorProduct.assoc ℝ W V V) (s ⊗ₜ[ℝ] b i))) ⊗ₜ[ℝ] b i))=s := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul w v =>
      simp only [TensorProduct.assoc_tmul,TensorProduct.map_tmul,LinearMap.id_apply,
        diagonalEvaluation_basis_right,TensorProduct.rid_tmul,← TensorProduct.smul_tmul',smul_smul]
      calc
        _ = ∑ i,b.equivFun v i • (w ⊗ₜ[ℝ] b i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← mul_assoc,hcd,one_mul]
        _ = w ⊗ₜ[ℝ] v := by
          simp_rw [← TensorProduct.tmul_smul]
          rw [← TensorProduct.tmul_sum]
          exact congrArg (fun y =>w ⊗ₜ[ℝ] y) (b.sum_repr v)
    | add s t hs ht =>
      simp only [TensorProduct.add_tmul,map_add,TensorProduct.add_tmul,smul_add,Finset.sum_add_distrib,hs,ht]
  exact hs (S x)

/-- Finite-dimensional bending is an actual linear equivalence, with inverse
given by literal evaluation and tensor associativity. -/
def finiteRightBendingEquiv (b : Module.Basis I ℝ V) (c d : I → ℝ)
    (hcd : ∀ i,c i*d i=1) :
    ((X ⊗[ℝ] V) →ₗ[ℝ] W) ≃ₗ[ℝ] (X →ₗ[ℝ] W ⊗[ℝ] V) where
  toFun T := bendRight T (diagonalCoevaluation b c)
  invFun S := unbendRight S (diagonalEvaluation b d)
  left_inv := unbendRight_bendRight_diagonal b c d hcd
  right_inv := bendRight_unbendRight_diagonal b c d hcd
  map_add' T U := by
    ext x
    simp only [bendRight_diagonal,LinearMap.add_apply,TensorProduct.add_tmul,smul_add,Finset.sum_add_distrib]
  map_smul' a T := by
    ext x
    simp only [bendRight_diagonal,LinearMap.smul_apply,← TensorProduct.smul_tmul',
      Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact smul_comm _ _ _

end AMSPhysical
#print axioms AMSPhysical.finiteRightBendingEquiv
