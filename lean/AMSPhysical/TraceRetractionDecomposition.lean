import BilinearOrthogonalSum
import Mathlib.LinearAlgebra.Trace

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
variable {I V : Type*} [Fintype I] [DecidableEq I] [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {W : I → Type*} [∀ i,AddCommGroup (W i)] [∀ i,Module ℝ (W i)] [∀ i,FiniteDimensional ℝ (W i)]

theorem trace_retraction_resolution (A : ∀ i,W i →ₗ[ℝ] V) (B : ∀ i,V →ₗ[ℝ] W i)
    (hSum : (∑ i,(A i).comp (B i))=LinearMap.id) (T : Module.End ℝ V) :
    LinearMap.trace ℝ V T=∑ i,LinearMap.trace ℝ (W i) ((B i).comp (T.comp (A i))) := by
  calc
    _ = LinearMap.trace ℝ V (T.comp (∑ i,(A i).comp (B i))) := by rw [hSum,LinearMap.comp_id]
    _ = ∑ i,LinearMap.trace ℝ V (T.comp ((A i).comp (B i))) := by
      have hs : T.comp (∑ i,(A i).comp (B i))=∑ i,T.comp ((A i).comp (B i)) := by
        apply LinearMap.ext
        intro v
        simp only [LinearMap.comp_apply,LinearMap.sum_apply,map_sum]
      rw [hs,map_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← LinearMap.comp_assoc,LinearMap.trace_comp_comm']

theorem trace_decomposition_of_retractions (A : ∀ i,W i →ₗ[ℝ] V) (B : ∀ i,V →ₗ[ℝ] W i)
    (hSum : (∑ i,(A i).comp (B i))=LinearMap.id) (hBA : ∀ i,(B i).comp (A i)=LinearMap.id)
    (T : Module.End ℝ V) (D : ∀ i,Module.End ℝ (W i))
    (hD : ∀ i,T.comp (A i)=(A i).comp (D i)) :
    LinearMap.trace ℝ V T=∑ i,LinearMap.trace ℝ (W i) (D i) := by
  rw [trace_retraction_resolution A B hSum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hD,← LinearMap.comp_assoc,hBA,LinearMap.id_comp]

def familyEquivProjection (S : I → Submodule ℝ V) (e : (∀ i,S i) ≃ₗ[ℝ] V) (i : I) : V →ₗ[ℝ] S i :=
  (LinearMap.proj i).comp e.symm.toLinearMap

theorem familyEquivProjection_resolution (S : I → Submodule ℝ V) (e : (∀ i,S i) ≃ₗ[ℝ] V)
    (he : e.toLinearMap=submoduleFamilySum S) :
    (∑ i,(S i).subtype.comp (familyEquivProjection S e i))=LinearMap.id := by
  apply LinearMap.ext
  intro v
  simp only [LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.id_apply]
  change (∑ i,((e.symm v) i).val)=v
  have h:=DFunLike.congr_fun he (e.symm v)
  change e (e.symm v)=(∑ i,((e.symm v) i).val) at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

theorem familyEquivProjection_subtype (S : I → Submodule ℝ V) (e : (∀ i,S i) ≃ₗ[ℝ] V)
    (he : e.toLinearMap=submoduleFamilySum S) (i : I) :
    (familyEquivProjection S e i).comp (S i).subtype=LinearMap.id := by
  apply LinearMap.ext
  intro v
  have hSingle : e (Pi.single i v)=v.val := by
    rw [show e (Pi.single i v)=submoduleFamilySum S (Pi.single i v) from DFunLike.congr_fun he _]
    exact submoduleFamilySum_single S i v
  have hSymm : e.symm v.val=Pi.single i v := by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply,hSingle]
  change (e.symm v.val) i=v
  rw [hSymm]
  simp only [Pi.single_eq_same]

end AMSPhysical
