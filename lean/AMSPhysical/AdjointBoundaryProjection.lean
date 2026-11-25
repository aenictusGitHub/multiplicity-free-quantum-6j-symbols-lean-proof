import DefiniteBilinearDuality

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
variable {V W V₂ W₂ : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup V₂] [Module ℝ V₂] [AddCommGroup W₂] [Module ℝ W₂]

theorem compressed_adjoint_pair
    (B : LinearMap.BilinForm ℝ V) (C : LinearMap.BilinForm ℝ W)
    (B₂ : LinearMap.BilinForm ℝ V₂) (C₂ : LinearMap.BilinForm ℝ W₂)
    (hC : ∀ v w,C v w=C w v) (hC₂ : ∀ v w,C₂ v w=C₂ w v)
    (E : V₂ →ₗ[ℝ] V) (P : V →ₗ[ℝ] V₂) (D : W₂ →ₗ[ℝ] W) (Q : W →ₗ[ℝ] W₂)
    (hEP : ∀ u v,B (E u) v=B₂ u (P v)) (hDQ : ∀ y w,C (D y) w=C₂ y (Q w))
    (F : V →ₗ[ℝ] W) (G : W →ₗ[ℝ] V) (hFG : ∀ v w,C (F v) w=B v (G w)) (u : V₂) (y : W₂) :
    C₂ (Q (F (E u))) y=B₂ u (P (G (D y))) := by
  calc
    _ = C₂ y (Q (F (E u))) := hC₂ _ _
    _ = C (D y) (F (E u)) := (hDQ _ _).symm
    _ = C (F (E u)) (D y) := hC _ _
    _ = B (E u) (G (D y)) := hFG _ _
    _ = _ := hEP _ _

/-- Exact full boundary projection naturality follows from independently
proved physical adjunctions and the actual adjoint boundary commuting square. -/
theorem adjoint_boundary_projection_naturality
    (B : LinearMap.BilinForm ℝ V) (C : LinearMap.BilinForm ℝ W)
    (B₂ : LinearMap.BilinForm ℝ V₂) (C₂ : LinearMap.BilinForm ℝ W₂)
    (hB : ∀ v w,B v w=B w v) (hC : ∀ v w,C v w=C w v)
    (hB₂ : ∀ v w,B₂ v w=B₂ w v) (hC₂ : ∀ v w,C₂ v w=C₂ w v)
    (hDef : ∀ w,C₂ w w=0 → w=0)
    (E : V₂ →ₗ[ℝ] V) (P : V →ₗ[ℝ] V₂) (D : W₂ →ₗ[ℝ] W) (Q : W →ₗ[ℝ] W₂)
    (hEP : ∀ u v,B (E u) v=B₂ u (P v)) (hDQ : ∀ y w,C (D y) w=C₂ y (Q w))
    (F : V →ₗ[ℝ] W) (G : W →ₗ[ℝ] V) (F₂ : V₂ →ₗ[ℝ] W₂) (G₂ : W₂ →ₗ[ℝ] V₂)
    (hFG : ∀ v w,C (F v) w=B v (G w)) (hFG₂ : ∀ u y,C₂ (F₂ u) y=B₂ u (G₂ y))
    (hSquare : ∀ y,G (D y)=E (G₂ y)) (v : V) : Q (F v)=F₂ (P v) := by
  apply definiteBilinear_injective C₂ hDef
  apply LinearMap.ext
  intro y
  calc
    _ = C₂ y (Q (F v)) := hC₂ _ _
    _ = C (D y) (F v) := (hDQ _ _).symm
    _ = C (F v) (D y) := hC _ _
    _ = B v (G (D y)) := hFG _ _
    _ = B v (E (G₂ y)) := by rw [hSquare]
    _ = B (E (G₂ y)) v := hB _ _
    _ = B₂ (G₂ y) (P v) := hEP _ _
    _ = B₂ (P v) (G₂ y) := hB₂ _ _
    _ = _ := (hFG₂ _ _).symm

end AMSPhysical
#print axioms AMSPhysical.adjoint_boundary_projection_naturality
