import Polar
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

set_option autoImplicit false
noncomputable section
open scoped ComplexOrder

namespace AMSPhysical

/-- Concrete finite complex matrix version: all functional-calculus instances
are supplied by Mathlib, not assumed as a replacement for the desired result. -/
theorem matrix_simultaneous_unitary (k : ℕ)
    (a₁ a₂ b₁ b₂ f : CStarMatrix (Fin k) (Fin k) ℂ) (hf : IsUnit f)
    (ha₁ : IsSelfAdjoint a₁) (ha₂ : IsSelfAdjoint a₂)
    (hb₁ : IsSelfAdjoint b₁) (hb₂ : IsSelfAdjoint b₂)
    (h₁ : b₁*f=f*a₁) (h₂ : b₂*f=f*a₂) :
    ∃ s : CStarMatrix (Fin k) (Fin k) ℂ,
      s ∈ unitary (CStarMatrix (Fin k) (Fin k) ℂ) ∧
        b₁*s=s*a₁ ∧ b₂*s=s*a₂ :=
  exists_simultaneous_unitary a₁ a₂ b₁ b₂ f hf ha₁ ha₂ hb₁ hb₂ h₁ h₂

end AMSPhysical
#print axioms AMSPhysical.matrix_simultaneous_unitary
