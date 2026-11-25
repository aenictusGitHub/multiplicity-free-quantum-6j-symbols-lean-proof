import BilinearCyclic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace AMSPhysical
variable {A V I : Type*} [Ring A] [Algebra ℝ A] [AddCommGroup V] [Module ℝ V]

theorem algebraInvariant_iSup (ρ : A →ₐ[ℝ] Module.End ℝ V)
    (S : I → Submodule ℝ V) (hS : ∀ i,algebraInvariant ρ (S i)) :
    algebraInvariant ρ (⨆ i,S i) := by
  intro z
  have hle : (⨆ i,S i)≤(⨆ i,S i).comap (ρ z) := by
    apply iSup_le
    intro i v hv
    exact (le_iSup S i) (hS i z v hv)
  exact hle

end AMSPhysical
