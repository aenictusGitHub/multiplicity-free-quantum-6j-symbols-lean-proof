import WeightedTranslation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {X : Type*} [AddCommGroup X]

def CoefficientSupported (P : X → Prop) (f : X →₀ ℝ) : Prop := ∀ x,f x≠0 → P x

theorem coefficientSupported_single (P : X → Prop) (x : X) (a : ℝ) (hx : P x) :
    CoefficientSupported P (Finsupp.single x a) := by
  classical
  intro y hy
  by_cases h : x=y
  · exact h ▸ hx
  · exact (hy (by simp only [Finsupp.single_apply,if_neg h])).elim

theorem coefficientSupported_weightedTranslation (P : X → Prop) (s : X) (w : X → ℝ)
    (hP : ∀ x,P x → P (x+s)) (f : X →₀ ℝ) (hf : CoefficientSupported P f) :
    CoefficientSupported P (weightedTranslation s w f) := by
  intro y hy
  rw [weightedTranslation_apply] at hy
  have h:=hP (y-s) (hf (y-s) (mul_ne_zero_iff.mp hy).1)
  simpa only [sub_add_cancel] using h

theorem coefficientSupported_sum {I : Type*} [Fintype I] (P : X → Prop) (f : I → X →₀ ℝ)
    (hf : ∀ i,CoefficientSupported P (f i)) : CoefficientSupported P (∑ i,f i) := by
  intro x hx
  rw [Finsupp.finset_sum_apply] at hx
  obtain ⟨i,hi,h⟩:=Finset.exists_ne_zero_of_sum_ne_zero hx
  exact hf i x h

theorem weightedTranslation_zero_on_support (s : X) (w : X → ℝ) (f : X →₀ ℝ)
    (hw : ∀ x,f x≠0 → w x=0) : weightedTranslation s w f=0 := by
  ext x
  rw [weightedTranslation_apply,Finsupp.zero_apply]
  by_cases hx : f (x-s)=0
  · rw [hx,zero_mul]
  · rw [hw _ hx,mul_zero]

end AMSPhysical
