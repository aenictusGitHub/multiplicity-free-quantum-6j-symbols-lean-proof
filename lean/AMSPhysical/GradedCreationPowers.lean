import GradedWeightedTranslation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {X : Type*} [AddCommGroup X]

theorem coefficientHomogeneous_single (d : X →+ ℤ) (x : X) (a : ℝ) :
    CoefficientHomogeneous d (d x) (Finsupp.single x a) := by
  classical
  intro y hy
  by_cases h : x=y
  · exact congrArg d h.symm
  · exact (hy (by simp only [Finsupp.single_apply,if_neg h])).elim

theorem sumWeightedTranslation_homogeneous {I : Type*} [Fintype I]
    (d : X →+ ℤ) (s : I → X) (w : I → X → ℝ) (δ : ℤ) (hs : ∀ i,d (s i)=δ)
    (a : ℤ) (f : X →₀ ℝ) (hf : CoefficientHomogeneous d a f) :
    CoefficientHomogeneous d (a+δ) ((∑ i,weightedTranslation (s i) (w i)) f) := by
  rw [LinearMap.sum_apply]
  apply coefficientHomogeneous_sum
  intro i
  have h:=coefficientHomogeneous_weightedTranslation d a f hf (s i) (w i)
  simpa only [hs i] using h

theorem gradedCreation_pow (d : X →+ ℤ) (R : Module.End ℝ (X →₀ ℝ)) (δ : ℤ)
    (hR : ∀ a f,CoefficientHomogeneous d a f → CoefficientHomogeneous d (a+δ) (R f))
    (a : ℤ) (f : X →₀ ℝ) (hf : CoefficientHomogeneous d a f) (t : ℕ) :
    CoefficientHomogeneous d (a+δ*(t:ℤ)) ((R^t) f) := by
  induction t with
  | zero => simpa only [Nat.cast_zero,mul_zero,add_zero,pow_zero,Module.End.one_apply] using hf
  | succ t ih =>
    have h:=hR (a+δ*(t:ℤ)) _ ih
    rw [show a+δ*((t+1:ℕ):ℤ)=a+δ*(t:ℤ)+δ by push_cast;ring,pow_succ',Module.End.mul_apply]
    exact h

end AMSPhysical
