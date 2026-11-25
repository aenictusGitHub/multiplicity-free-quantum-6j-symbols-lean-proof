import BilinearAdjoint

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace AMSPhysical
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

theorem scaledAdjoint_radial_selfAdjoint (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (C : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (hB : ∀ v w,B v w=B w v) (hC : ∀ v w,C v w=C w v)
    (R : V →ₗ[ℝ] W) (L : W →ₗ[ℝ] V) (κ : ℝ)
    (hAdj : ∀ v w,C (R v) w=B v (κ • L w)) (u v : W) :
    C (R (L u)) v=C u (R (L v)) := by
  have h:=hAdj (L u) v
  have h':=hAdj (L v) u
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul] at h h'
  rw [hB] at h
  exact h.trans (h'.symm.trans (hC _ _))

end AMSPhysical
