import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct
variable {K V W I J T : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [Fintype T]

theorem tensor_basis_diagonal_coefficient (b : Basis I K V) (d : Basis J K W)
    (f : T → I) (g : T → J) (hf : Function.Injective f) (c : T → K) (t : T) :
    (b.tensorProduct d).repr (∑ u,c u • (b (f u) ⊗ₜ[K] d (g u))) (f t,g t)=c t := by
  classical
  simp [map_sum,Finsupp.sum_apply,Finsupp.smul_apply,Module.Basis.tensorProduct_repr_tmul_apply,
    Module.Basis.repr_self,Finsupp.single_apply,hf.eq_iff,eq_comm]

theorem tensor_basis_diagonal_ne_zero (b : Basis I K V) (d : Basis J K W)
    (f : T → I) (g : T → J) (hf : Function.Injective f) (c : T → K) (t : T) (ht : c t≠0) :
    (∑ u,c u • (b (f u) ⊗ₜ[K] d (g u)))≠0 := by
  intro hz
  have he := tensor_basis_diagonal_coefficient b d f g hf c t
  rw [hz,map_zero,Finsupp.zero_apply] at he
  exact ht he.symm

end AMSPhysical
#print axioms AMSPhysical.tensor_basis_diagonal_ne_zero
