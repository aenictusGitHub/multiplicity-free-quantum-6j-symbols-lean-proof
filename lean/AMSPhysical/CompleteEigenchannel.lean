import BilinearOrthogonalSum
import Mathlib.LinearAlgebra.Eigenspace.Basic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical
variable {V I : Type*} [AddCommGroup V] [Module ℝ V] [Fintype I] [DecidableEq I]

/-- In a complete direct sum of distinct scalar channels, the eigenspaces
of the actual operator equal those channels, in both directions. -/
theorem completeEigenchannel_eq (S : I → Submodule ℝ V)
    (hsum : Function.Bijective (submoduleFamilySum S)) (A : Module.End ℝ V) (lam : I → ℝ)
    (hinj : Function.Injective lam) (hA : ∀ i,∀ v∈S i,A v=lam i • v) (j : I) :
    A.eigenspace (lam j)=S j := by
  ext v
  constructor
  · intro hv
    have hAv : A v=lam j • v := Module.End.mem_eigenspace_iff.mp hv
    obtain ⟨x,hx⟩:=hsum.2 v
    have he : submoduleFamilySum S (fun i =>lam i • x i)=submoduleFamilySum S (fun i =>lam j • x i) := by
      change (∑ i,lam i • (x i).val)=∑ i,lam j • (x i).val
      calc
        _ = A (submoduleFamilySum S x) := by
          change (∑ i,lam i • (x i).val)=A (∑ i,(x i).val)
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro i hi
          exact (hA i _ (x i).property).symm
        _ = lam j • v := by rw [hx,hAv]
        _ = _ := by
          rw [← hx]
          change lam j • (∑ i,(x i).val)=∑ i,lam j • (x i).val
          rw [Finset.smul_sum]
    have hc (i : I) (hi : i≠j) : x i=0 := by
      have hh:=congrArg Subtype.val (congrFun (hsum.1 he) i)
      change lam i • (x i).val=lam j • (x i).val at hh
      have hz : (lam i-lam j) • (x i).val=0 := by rw [sub_smul,hh,sub_self]
      apply Subtype.ext
      exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (fun he =>hi (hinj he)))
    have hsingle : x=Pi.single j (x j) := by
      funext i
      by_cases hi : i=j
      · subst i;simp
      · simp [Pi.single_apply,hi,Ne.symm hi,hc i hi]
    rw [← hx,hsingle,submoduleFamilySum_single]
    exact (x j).property
  · intro hv
    exact Module.End.mem_eigenspace_iff.mpr (hA j v hv)

end AMSPhysical
#print axioms AMSPhysical.completeEigenchannel_eq
