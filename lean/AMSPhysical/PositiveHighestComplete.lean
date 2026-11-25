import BilinearCyclic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
variable {A V : Type*} [Ring A] [Algebra ℝ A] [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V]

/-- A positive adjoint-closed representation is exhausted by an invariant
subspace containing all highest vectors, provided highest vectors exist in
every nonzero invariant subspace. Orthogonal complementation proves this. -/
theorem positive_invariant_complete_of_highest (ρ : A →ₐ[ℝ] Module.End ℝ V)
    (B : LinearMap.BilinForm ℝ V) (hSym : ∀ x y,B x y=B y x)
    (hDef : ∀ x,B x x=0 → x=0)
    (hAdj : ∀ z : A,∃ u : A,PairAdjoint B (ρ z) (ρ u))
    (P : V → Prop) (S : Submodule ℝ V) (hS : algebraInvariant ρ S)
    (hAll : ∀ w,P w → w∈S)
    (hExists : ∀ T : Submodule ℝ V,algebraInvariant ρ T → T≠⊥ → ∃ w,w∈T ∧ w≠0 ∧ P w) : S=⊤ := by
  have hR : LinearMap.BilinForm.IsRefl B := by
    intro x y h
    change B y x=0
    rw [← hSym x y]
    exact h
  have hND : (LinearMap.BilinForm.restrict B S).Nondegenerate := by
    intro x hx
    apply Subtype.ext
    exact hDef x.val (hx x)
  have hCompl := LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate (B:=B) hR hND
  have hO := algebraInvariant_orthogonal ρ B hSym hAdj S hS
  have hO0 : LinearMap.BilinForm.orthogonal B S=⊥ := by
    by_contra hn0
    obtain ⟨w,hw,hw0,hwP⟩ := hExists _ hO hn0
    exact hw0 (hDef w (hw w (hAll w hwP)))
  have ht := hCompl.sup_eq_top
  rw [hO0,sup_bot_eq] at ht
  exact ht

end AMSPhysical
