import BilinearOrthonormal
import Mathlib.LinearAlgebra.Basis.Defs

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
noncomputable section
namespace AMSPhysical
open Module
variable {ι κ V : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [AddCommGroup V] [Module ℝ V]

theorem orthonormal_basis_coord_right (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (b : Basis ι ℝ V)
    (hb : ∀ i j,B (b i) (b j)=if i=j then 1 else 0) (i : ι) (v : V) :
    B (b i) v=b.repr v i := by
  conv_lhs => rw [← b.sum_repr v]
  simp only [map_sum,map_smul,smul_eq_mul,hb,mul_ite,mul_one,mul_zero]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem orthonormal_basis_coord_left (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (b : Basis ι ℝ V)
    (hb : ∀ i j,B (b i) (b j)=if i=j then 1 else 0) (i : ι) (v : V) :
    B v (b i)=b.repr v i := by
  conv_lhs => rw [← b.sum_repr v]
  simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,smul_eq_mul,hb,
    mul_ite,mul_one,mul_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem orthonormal_basis_parseval (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (b : Basis ι ℝ V)
    (hb : ∀ i j,B (b i) (b j)=if i=j then 1 else 0) (p v : V) :
    (∑ i,B p (b i)*B v (b i))=B p v := by
  have he := congrArg (fun w => B w v) (b.sum_repr p)
  simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,smul_eq_mul] at he
  calc
    _=∑ i,b.repr p i*B (b i) v := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [orthonormal_basis_coord_left B b hb i p,orthonormal_basis_coord_left B b hb i v,
        orthonormal_basis_coord_right B b hb i v]
    _=B p v := he

theorem orthonormal_basis_symm (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (b : Basis ι ℝ V)
    (hb : ∀ i j,B (b i) (b j)=if i=j then 1 else 0) (p v : V) : B p v=B v p := by
  rw [← orthonormal_basis_parseval B b hb p v,← orthonormal_basis_parseval B b hb v p]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem orthonormal_basis_change_rows (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (b : Basis ι ℝ V) (c : Basis κ ℝ V)
    (hb : ∀ i j,B (b i) (b j)=if i=j then 1 else 0)
    (hc : ∀ i j,B (c i) (c j)=if i=j then 1 else 0) (i j : ι) :
    (∑ k,B (b i) (c k)*B (b j) (c k))=if i=j then 1 else 0 := by
  rw [orthonormal_basis_parseval B c hc,hb]

theorem orthonormal_basis_change_cols (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (b : Basis ι ℝ V) (c : Basis κ ℝ V)
    (hb : ∀ i j,B (b i) (b j)=if i=j then 1 else 0)
    (hc : ∀ i j,B (c i) (c j)=if i=j then 1 else 0) (i j : κ) :
    (∑ k,B (b k) (c i)*B (b k) (c j))=if i=j then 1 else 0 := by
  calc
    _=∑ k,B (c i) (b k)*B (c j) (b k) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact congrArg₂ (·*·) (orthonormal_basis_symm B b hb (b k) (c i))
        (orthonormal_basis_symm B b hb (b k) (c j))
    _=B (c i) (c j) := orthonormal_basis_parseval B b hb (c i) (c j)
    _=_ := hc i j

end AMSPhysical

#print axioms AMSPhysical.orthonormal_basis_change_rows
#print axioms AMSPhysical.orthonormal_basis_change_cols
