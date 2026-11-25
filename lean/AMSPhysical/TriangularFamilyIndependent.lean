import TriangularCoordinates
import Mathlib.LinearAlgebra.LinearIndependent.Defs

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace AMSPhysical
variable {I V : Type*} [Fintype I] [DecidableEq I] [AddCommGroup V] [Module ℝ V]

/-- Nonzero triangular coordinates prove independence of the actual vectors. -/
theorem triangularFamily_linearIndependent (b : I → V) (index : I → ℕ)
    (hinj : Function.Injective index) (coord : ℕ → V →ₗ[ℝ] ℝ)
    (htri : ∀ i y,y < index i → coord y (b i)=0)
    (hdiag : ∀ i,coord (index i) (b i)≠0) : LinearIndependent ℝ b := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  exact triangular_expansion_cutoff b index hinj coord htri hdiag c 0 hc (index i+1)
    (by intro y hy;exact map_zero _) i (by omega)

end AMSPhysical
