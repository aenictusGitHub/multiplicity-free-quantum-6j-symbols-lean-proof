import KroneckerEigenExpansion
import BilinearCyclic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace AMSPhysical
variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype I] [DecidableEq I]

theorem eigenvector_zero_of_disjoint_expansion (A : Module.End K V) (b : I → V) (lam : I → K)
    (hb : LinearIndependent K b) (hA : ∀ i,A (b i)=lam i • b i) (v : V) (c : I → K) (a : K)
    (hv : v=∑ i,c i • b i) (hAv : A v=a • v) (hNe : ∀ i,lam i≠a) : v=0 := by
  have he : (∑ i,(c i*lam i) • b i)=∑ i,(a*c i) • b i := by
    calc
      _ = A (∑ i,c i • b i) := by simp only [map_sum,map_smul,hA,smul_smul]
      _ = A v := congrArg A hv.symm
      _ = a • v := hAv
      _ = _ := by rw [hv,Finset.smul_sum];simp only [smul_smul]
  have hc : ∀ i,c i=0 := by
    intro i
    have hh:=hb.eq_coords_of_eq he i
    have hz : c i*(lam i-a)=0 := by linear_combination hh
    exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr (hNe i))
  rw [hv]
  simp only [hc,zero_smul,Finset.sum_const_zero]

theorem intertwiner_zero_on_cyclic {A V W : Type*} [Ring A] [Algebra ℝ A]
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (ρ : A →ₐ[ℝ] Module.End ℝ V) (σ : A →ₐ[ℝ] Module.End ℝ W)
    (T : V →ₗ[ℝ] W) (hT : ∀ z v,T (ρ z v)=σ z (T v)) (v : V) (hv : T v=0)
    (w : V) (hw : w∈algebraCyclicSpan ρ v) : T w=0 := by
  induction hw using Submodule.span_induction with
  | mem x hx => obtain ⟨z,rfl⟩ := hx;rw [hT,hv,map_zero]
  | zero => exact map_zero T
  | add x y hx hy hix hiy => rw [map_add,hix,hiy,add_zero]
  | smul c x hx hix => rw [map_smul,hix,smul_zero]

end AMSPhysical
