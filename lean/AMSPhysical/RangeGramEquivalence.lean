import LinearCombinationGram
import Mathlib.LinearAlgebra.Isomorphisms

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
variable {X V W : Type*} [AddCommGroup X] [Module ℝ X]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

def sameKernelRangeEquiv (f : X →ₗ[ℝ] V) (g : X →ₗ[ℝ] W) (h : LinearMap.ker f=LinearMap.ker g) :
    LinearMap.range f ≃ₗ[ℝ] LinearMap.range g :=
  (f.quotKerEquivRange.symm.trans (Submodule.quotEquivOfEq _ _ h)).trans g.quotKerEquivRange

theorem sameKernelRangeEquiv_image (f : X →ₗ[ℝ] V) (g : X →ₗ[ℝ] W)
    (h : LinearMap.ker f=LinearMap.ker g) (x : X) (hx : f x∈LinearMap.range f) :
    (sameKernelRangeEquiv f g h ⟨f x,hx⟩).val=g x := by
  simp only [sameKernelRangeEquiv,LinearEquiv.trans_apply,LinearMap.quotKerEquivRange_symm_apply_image,
    Submodule.mkQ_apply,Submodule.quotEquivOfEq_mk,LinearMap.quotKerEquivRange_apply_mk]

/-- The induced equivalence of positive Gram realizations is an actual
bilinear isometry, proved on all vectors in both ranges. -/
theorem sameKernelRangeEquiv_isometry (f : X →ₗ[ℝ] V) (g : X →ₗ[ℝ] W)
    (h : LinearMap.ker f=LinearMap.ker g)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (C : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (hGram : ∀ x y,B (f x) (f y)=C (g x) (g y))
    (u v : LinearMap.range f) :
    B u.val v.val=C (sameKernelRangeEquiv f g h u).val (sameKernelRangeEquiv f g h v).val := by
  rcases u with ⟨u,hu⟩
  rcases v with ⟨v,hv⟩
  obtain ⟨x,rfl⟩ := hu
  obtain ⟨y,rfl⟩ := hv
  rw [sameKernelRangeEquiv_image,sameKernelRangeEquiv_image]
  exact hGram x y

end AMSPhysical
#print axioms AMSPhysical.sameKernelRangeEquiv_isometry
