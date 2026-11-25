import BilinearMetricAdjoint
import CompactJointAdjoint

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W]

theorem compact_bilinearMetricAdjoint_intertwines (q : ℝ) (n : ℕ)
    (ρ : UqTypeA q n →ₐ[ℝ] Module.End ℝ V) (σ : UqTypeA q n →ₐ[ℝ] Module.End ℝ W)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (C : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (hB : IsCompactTypeAPair q n B ρ) (hC : IsCompactTypeAPair q n C σ)
    (hDefB : ∀ v,B v v=0 → v=0) (hSymB : ∀ v w,B v w=B w v) (hSymC : ∀ v w,C v w=C w v)
    (T : V →ₗ[ℝ] W) (hT : ∀ z v,T (ρ z v)=σ z (T v)) (z : UqTypeA q n) (w : W) :
    bilinearMetricAdjoint B C hDefB T (σ z w)=ρ z (bilinearMetricAdjoint B C hDefB T w) :=
  compact_intertwiner_adjoint B C ρ σ hB hC (definiteBilinear_injective B hDefB) hSymB hSymC
    T (bilinearMetricAdjoint B C hDefB T) hT (bilinearMetricAdjoint_adjoint B C hDefB hSymB hSymC T) z w

end AMSPhysical
