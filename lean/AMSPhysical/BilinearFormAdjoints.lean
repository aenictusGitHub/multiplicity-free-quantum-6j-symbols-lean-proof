import BilinearAdjoint

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace AMSPhysical
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

theorem pairAdjoint_form_sub (B C : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (A : Module.End ℝ V)
    (hB : PairAdjoint B A A) (hC : PairAdjoint C A A) : PairAdjoint (B-C) A A := by
  intro v w
  change B (A v) w-C (A v) w=B v (A w)-C v (A w)
  rw [hB,hC]

theorem pairAdjoint_form_smul (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (A : Module.End ℝ V)
    (hB : PairAdjoint B A A) (a : ℝ) : PairAdjoint (a • B) A A := by
  intro v w
  change a*B (A v) w=a*B v (A w)
  rw [hB]

theorem pairAdjoint_pullback_intertwiner (C : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (f : V →ₗ[ℝ] W)
    (A : Module.End ℝ V) (D : Module.End ℝ W) (hD : PairAdjoint C D D)
    (hf : ∀ v,f (A v)=D (f v)) : PairAdjoint ((C.comp f).compl₂ f) A A := by
  intro v w
  change C (f (A v)) (f w)=C (f v) (f (A w))
  rw [hf v,hf w,hD]

end AMSPhysical
