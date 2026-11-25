import FiniteWeightedHilbert
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
open Module
variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℝ V]

theorem finiteWeightedPair_basis_right (b : Basis ι ℝ V) (w : ι → ℝ) (v : V) (i : ι) :
    finiteWeightedPair w b.equivFun.toLinearMap v (b i)=w i*b.equivFun v i := by
  classical
  simp [finiteWeightedPair,Basis.equivFun_self,Pi.single_apply,eq_comm]

theorem finiteWeightedBilin_injective (b : Basis ι ℝ V) (w : ι → ℝ) (hw : ∀ i,w i≠0) :
    Function.Injective (finiteWeightedBilin w b.equivFun.toLinearMap) := by
  intro v u he
  apply b.equivFun.injective
  funext i
  have hh := DFunLike.congr_fun he (b i)
  change finiteWeightedPair w b.equivFun.toLinearMap v (b i)=
    finiteWeightedPair w b.equivFun.toLinearMap u (b i) at hh
  rw [finiteWeightedPair_basis_right,finiteWeightedPair_basis_right] at hh
  exact mul_left_cancel₀ (hw i) hh

/-- A nonzero diagonal bilinear form gives a constructed perfect duality. -/
def finiteWeightedDuality (b : Basis ι ℝ V) (w : ι → ℝ) (hw : ∀ i,w i≠0) :
    V ≃ₗ[ℝ] Module.Dual ℝ V := by
  letI : Module.Finite ℝ V := Module.Finite.of_basis b
  exact LinearEquiv.ofBijective (finiteWeightedBilin w b.equivFun.toLinearMap)
    ⟨finiteWeightedBilin_injective b w hw,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (Subspace.dual_finrank_eq (K:=ℝ) (V:=V)).symm).mp (finiteWeightedBilin_injective b w hw)⟩

end AMSPhysical
#print axioms AMSPhysical.finiteWeightedDuality
