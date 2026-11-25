import CompactTypeAPair

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace AMSPhysical
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem pairAdjoint_form_scale (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (A D : Module.End ℝ V)
    (h : PairAdjoint B A D) (c : ℝ) : PairAdjoint (c • B) A D := by
  intro v w
  change c*B (A v) w=c*B v (D w)
  rw [h]

theorem compactTypeAPair_scale (q : ℝ) (n : ℕ) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (h : IsCompactTypeAPair q n B ρ) (c : ℝ) :
    IsCompactTypeAPair q n (c • B) ρ :=
  ⟨fun i =>pairAdjoint_form_scale B _ _ (h.adjE i) c,
    fun i =>pairAdjoint_form_scale B _ _ (h.adjF i) c,
    fun i =>pairAdjoint_form_scale B _ _ (h.adjK i) c,
    fun i =>pairAdjoint_form_scale B _ _ (h.adjKi i) c⟩

end AMSPhysical
