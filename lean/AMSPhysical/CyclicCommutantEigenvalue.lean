import BilinearCyclic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace AMSPhysical
variable {A V : Type*} [Ring A] [Algebra ℝ A] [AddCommGroup V] [Module ℝ V]

theorem commutant_eigen_on_cyclic (ρ : A →ₐ[ℝ] Module.End ℝ V) (T : Module.End ℝ V)
    (hT : ∀ z v,T (ρ z v)=ρ z (T v)) (v : V) (a : ℝ) (hv : T v=a • v)
    (w : V) (hw : w∈algebraCyclicSpan ρ v) : T w=a • w := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z,rfl⟩ := hx
    rw [hT,hv,map_smul]
  | zero => simp
  | add x y hx hy hix hiy => rw [map_add,hix,hiy,smul_add]
  | smul c x hx hix => rw [map_smul,hix,smul_comm]

end AMSPhysical
