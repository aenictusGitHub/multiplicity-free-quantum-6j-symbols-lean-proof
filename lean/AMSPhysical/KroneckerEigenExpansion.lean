import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype I] [DecidableEq I]

theorem linearIndependent_of_kronecker_functionals (b : I → V) (C : I → Module.Dual K V)
    (hC : ∀ i j,C i (b j)=if j=i then 1 else 0) : LinearIndependent K b := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h:=congrArg (C i) hc
  simpa only [map_sum,map_smul,hC,map_zero,smul_eq_mul,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,if_true] using h

/-- A proved finite expansion in independent eigenvectors with distinct
eigenvalues has one-dimensional eigenspaces. -/
theorem eigenvector_of_distinct_expansion (A : Module.End K V) (b : I → V) (lam : I → K)
    (hb : LinearIndependent K b) (hlam : Function.Injective lam)
    (hA : ∀ i,A (b i)=lam i • b i) (v : V) (c : I → K) (r : I)
    (hv : v=∑ i,c i • b i) (hAv : A v=lam r • v) : v=c r • b r := by
  classical
  have he : (∑ i,(c i*lam i) • b i)=∑ i,(lam r*c i) • b i := by
    calc
      _ = A (∑ i,c i • b i) := by simp only [map_sum,map_smul,hA,smul_smul]
      _ = A v := congrArg A hv.symm
      _ = lam r • v := hAv
      _ = _ := by rw [hv,Finset.smul_sum];simp only [smul_smul]
  have hc : ∀ i,i≠r → c i=0 := by
    intro i hir
    have hh:=hb.eq_coords_of_eq he i
    have hz : c i*(lam i-lam r)=0 := by linear_combination hh
    exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr (fun h => hir (hlam h)))
  apply hv.trans
  apply Finset.sum_eq_single r
  · intro i hi hir
    rw [hc i hir,zero_smul]
  · simp

end AMSPhysical
