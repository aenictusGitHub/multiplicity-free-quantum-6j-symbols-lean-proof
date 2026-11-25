import CoefficientSupport

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {X : Type*} [AddCommGroup X]

theorem coefficientSupported_pow (P : X → Prop) (R : Module.End ℝ (X →₀ ℝ))
    (hR : ∀ f,CoefficientSupported P f → CoefficientSupported P (R f))
    (f : X →₀ ℝ) (hf : CoefficientSupported P f) (t : ℕ) : CoefficientSupported P ((R^t) f) := by
  induction t with
  | zero => simpa only [pow_zero,Module.End.one_apply] using hf
  | succ t ih =>
    have hp : (R^(t+1)) f=R ((R^t) f) := DFunLike.congr_fun (pow_succ' R t) f
    rw [hp]
    exact hR _ ih

end AMSPhysical
