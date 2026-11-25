import WeightedTranslation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
noncomputable section
namespace AMSPhysical
variable {X : Type*} [AddCommGroup X]

def CoefficientHomogeneous (d : X →+ ℤ) (a : ℤ) (f : X →₀ ℝ) : Prop :=
  ∀ x,f x≠0 → d x=a

theorem coefficientHomogeneous_weightedTranslation (d : X →+ ℤ) (a : ℤ)
    (f : X →₀ ℝ) (hf : CoefficientHomogeneous d a f) (s : X) (w : X → ℝ) :
    CoefficientHomogeneous d (a+d s) (weightedTranslation s w f) := by
  intro x hx
  rw [weightedTranslation_apply] at hx
  have h:=hf (x-s) (mul_ne_zero_iff.mp hx).1
  rw [map_sub] at h
  omega

theorem coefficientHomogeneous_sum {I : Type*} [Fintype I] (d : X →+ ℤ) (a : ℤ)
    (f : I → X →₀ ℝ) (hf : ∀ i,CoefficientHomogeneous d a (f i)) :
    CoefficientHomogeneous d a (∑ i,f i) := by
  intro x hx
  rw [Finsupp.finset_sum_apply] at hx
  obtain ⟨i,hi,h⟩:=Finset.exists_ne_zero_of_sum_ne_zero hx
  exact hf i x h

theorem weightedTranslation_zero_homogeneous (d : X →+ ℤ) (a : ℤ)
    (f : X →₀ ℝ) (hf : CoefficientHomogeneous d a f) (w : ℤ → ℝ) :
    weightedTranslation 0 (fun x =>w (d x)) f=w a • f := by
  ext x
  simp only [weightedTranslation_apply,sub_zero,Finsupp.smul_apply,smul_eq_mul]
  by_cases hx : f x=0
  · simp only [hx,zero_mul,mul_zero]
  · rw [hf x hx,mul_comm]

end AMSPhysical
