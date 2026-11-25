import Mathlib.Algebra.Algebra.Hom
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace AMSPhysical
variable {A V W : Type*} [Ring A] [Algebra ℝ A]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

theorem inverse_involutiveTwistedIntertwiner (ρ : A →ₐ[ℝ] Module.End ℝ V) (σ : A →ₐ[ℝ] Module.End ℝ W)
    (τ : A →ₐ[ℝ] A) (hτ : Function.Involutive τ) (f : V ≃ₗ[ℝ] W)
    (hf : ∀ z v,f (ρ z v)=σ (τ z) (f v)) (z : A) (w : W) :
    f.symm (σ z w)=ρ (τ z) (f.symm w) := by
  apply f.injective
  rw [f.apply_symm_apply,hf,hτ,f.apply_symm_apply]

end AMSPhysical
