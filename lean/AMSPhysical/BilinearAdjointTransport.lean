import BilinearMetricAdjoint
import TensorWeightedIsometries

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical
variable {V W V' W' : Type*}
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup V'] [Module ℝ V'] [AddCommGroup W'] [Module ℝ W']

theorem bilinearAdjoint_transport (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (C : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (B' : V' →ₗ[ℝ] V' →ₗ[ℝ] ℝ) (C' : W' →ₗ[ℝ] W' →ₗ[ℝ] ℝ)
    (e : V ≃ₗ[ℝ] V') (f : W ≃ₗ[ℝ] W')
    (he : ∀ v w,B' (e v) (e w)=B v w) (hf : ∀ v w,C' (f v) (f w)=C v w)
    (T : V →ₗ[ℝ] W) (D : W →ₗ[ℝ] V) (hD : ∀ v w,C (T v) w=B v (D w)) (v : V') (w : W') :
    C' (f (T (e.symm v))) w=B' v (e (D (f.symm w))) := by
  calc
    _ = C' (f (T (e.symm v))) (f (f.symm w)) := by rw [LinearEquiv.apply_symm_apply]
    _ = C (T (e.symm v)) (f.symm w) := hf _ _
    _ = B (e.symm v) (D (f.symm w)) := hD _ _
    _ = B' (e (e.symm v)) (e (D (f.symm w))) := (he _ _).symm
    _ = _ := by rw [LinearEquiv.apply_symm_apply]

theorem bilinearAdjoint_unique (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hB : ∀ v,B v v=0 → v=0) (hSym : ∀ v w,B v w=B w v)
    (C : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (T : V →ₗ[ℝ] W) (D E : W →ₗ[ℝ] V)
    (hD : ∀ v w,C (T v) w=B v (D w)) (hE : ∀ v w,C (T v) w=B v (E w)) : D=E := by
  apply LinearMap.ext
  intro w
  apply definiteBilinear_injective B hB
  apply LinearMap.ext
  intro v
  change B (D w) v=B (E w) v
  rw [hSym,hSym (E w),← hD,← hE]

end AMSPhysical
#print axioms AMSPhysical.bilinearAdjoint_transport
#print axioms AMSPhysical.bilinearAdjoint_unique
