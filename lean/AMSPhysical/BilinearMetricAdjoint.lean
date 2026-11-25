import DefiniteBilinearDuality

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W]

def bilinearMetricAdjoint (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (C : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (hB : ∀ v,B v v=0 → v=0) (T : V →ₗ[ℝ] W) : W →ₗ[ℝ] V :=
  (definiteBilinearDuality B hB).symm.toLinearMap.comp (T.dualMap.comp C)

theorem bilinearMetricAdjoint_adjoint (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (C : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (hB : ∀ v,B v v=0 → v=0) (hSymB : ∀ v w,B v w=B w v) (hSymC : ∀ v w,C v w=C w v)
    (T : V →ₗ[ℝ] W) (v : V) (w : W) :
    C (T v) w=B v (bilinearMetricAdjoint B C hB T w) := by
  have h:=congrArg (fun f : Module.Dual ℝ V =>f v)
    ((definiteBilinearDuality B hB).apply_symm_apply (T.dualMap (C w)))
  change B (bilinearMetricAdjoint B C hB T w) v=C w (T v) at h
  rw [hSymB,hSymC] at h
  exact h.symm

theorem bilinearMetricAdjoint_isometry_leftInverse (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (C : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (hB : ∀ v,B v v=0 → v=0) (hSymB : ∀ v w,B v w=B w v) (hSymC : ∀ v w,C v w=C w v)
    (T : V →ₗ[ℝ] W) (hT : ∀ v w,C (T v) (T w)=B v w) (v : V) :
    bilinearMetricAdjoint B C hB T (T v)=v := by
  apply definiteBilinear_injective B hB
  apply LinearMap.ext
  intro w
  calc
    _ = B w (bilinearMetricAdjoint B C hB T (T v)) := hSymB _ _
    _ = C (T w) (T v) := (bilinearMetricAdjoint_adjoint B C hB hSymB hSymC T w (T v)).symm
    _ = B w v := hT _ _
    _ = B v w := hSymB _ _

end AMSPhysical
