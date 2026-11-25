import FiniteWeightedHilbert
import BilinearAdjoint
import Mathlib.LinearAlgebra.TensorProduct.Basis

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000
noncomputable section
namespace AMSPhysical
open Module
open scoped TensorProduct
variable {ι κ V W : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

def tensorWeightedBilin (b : Basis ι ℝ V) (c : Basis κ ℝ W) (w : ι → ℝ) (z : κ → ℝ) :
    (V ⊗[ℝ] W) →ₗ[ℝ] (V ⊗[ℝ] W) →ₗ[ℝ] ℝ :=
  finiteWeightedBilin (fun ij : ι × κ => w ij.1*z ij.2) (b.tensorProduct c).equivFun.toLinearMap

theorem tensorWeightedBilin_tmul (b : Basis ι ℝ V) (c : Basis κ ℝ W) (w : ι → ℝ) (z : κ → ℝ)
    (p p' : V) (v v' : W) :
    tensorWeightedBilin b c w z (p ⊗ₜ[ℝ] v) (p' ⊗ₜ[ℝ] v')=
      finiteWeightedPair w b.equivFun.toLinearMap p p' * finiteWeightedPair z c.equivFun.toLinearMap v v' := by
  change (∑ ij : ι × κ,w ij.1*z ij.2*(b.tensorProduct c).equivFun (p ⊗ₜ[ℝ] v) ij *
    (b.tensorProduct c).equivFun (p' ⊗ₜ[ℝ] v') ij)=_
  simp only [Basis.equivFun_apply]
  rw [Fintype.sum_prod_type]
  simp only [Basis.tensorProduct_repr_tmul_apply,smul_eq_mul]
  unfold finiteWeightedPair
  simp only [LinearEquiv.coe_coe,Basis.equivFun_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem tensorWeightedBilin_adjoint_map (b : Basis ι ℝ V) (c : Basis κ ℝ W)
    (w : ι → ℝ) (z : κ → ℝ) (A A' : Module.End ℝ V) (D D' : Module.End ℝ W)
    (hA : PairAdjoint (finiteWeightedBilin w b.equivFun.toLinearMap) A A')
    (hD : PairAdjoint (finiteWeightedBilin z c.equivFun.toLinearMap) D D') :
    PairAdjoint (tensorWeightedBilin b c w z) (TensorProduct.map A D) (TensorProduct.map A' D') := by
  apply finiteWeightedAdjoint_of_basis (b.tensorProduct c)
  intro ij kl
  change tensorWeightedBilin b c w z _ _=tensorWeightedBilin b c w z _ _
  rw [Basis.tensorProduct_apply',Basis.tensorProduct_apply',TensorProduct.map_tmul,
    TensorProduct.map_tmul,tensorWeightedBilin_tmul,tensorWeightedBilin_tmul]
  exact congrArg₂ (·*·) (hA (b ij.1) (b kl.1)) (hD (c ij.2) (c kl.2))

end AMSPhysical

#print axioms AMSPhysical.tensorWeightedBilin_adjoint_map
