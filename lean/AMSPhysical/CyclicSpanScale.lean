import BilinearCyclic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace AMSPhysical
variable {A V : Type*} [Ring A] [Algebra ℝ A] [AddCommGroup V] [Module ℝ V]

theorem algebraCyclicSpan_smul (ρ : A →ₐ[ℝ] Module.End ℝ V) (v : V) (s : ℝ) (hs : s≠0) :
    algebraCyclicSpan ρ (s • v)=algebraCyclicSpan ρ v := by
  apply le_antisymm
  · exact algebraCyclicSpan_minimal ρ (s • v) _ (algebraCyclicSpan_invariant ρ v)
      ((algebraCyclicSpan ρ v).smul_mem s (algebraCyclicSpan_self ρ v))
  · apply algebraCyclicSpan_minimal ρ v _ (algebraCyclicSpan_invariant ρ (s • v))
    exact ((algebraCyclicSpan ρ (s • v)).smul_mem_iff hs).mp (algebraCyclicSpan_self ρ (s • v))

end AMSPhysical
#print axioms AMSPhysical.algebraCyclicSpan_smul
