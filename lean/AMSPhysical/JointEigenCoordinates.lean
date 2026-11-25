import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace AMSPhysical
open Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]

theorem eigenbasis_repr (b : Basis ι K V) (T : Module.End K V) (c : ι → K)
    (hT : ∀ i,T (b i)=c i • b i) (v : V) (i : ι) : b.repr (T v) i=c i*b.repr v i := by
  have he : T v=∑ j,b.repr v j • (c j • b j) := by
    conv_lhs => rw [← b.sum_repr v]
    simp only [map_sum,map_smul,hT]
  rw [he,map_sum]
  simp [map_smul,smul_smul,Finsupp.single_apply,mul_comm]

/-- A joint eigenvector with an eigenvalue pair absent from a complete joint
eigenbasis must vanish. -/
theorem joint_eigenvector_zero (b : Basis ι K V) (C H : Module.End K V) (c w : ι → K)
    (hC : ∀ i,C (b i)=c i • b i) (hH : ∀ i,H (b i)=w i • b i)
    (v : V) (c₀ w₀ : K) (hvC : C v=c₀ • v) (hvH : H v=w₀ • v)
    (hsep : ∀ i,c i≠c₀ ∨ w i≠w₀) : v=0 := by
  apply b.repr.injective
  apply Finsupp.ext
  intro i
  rw [map_zero,Finsupp.zero_apply]
  have hc := congrArg (fun x => b.repr x i) hvC
  have hw := congrArg (fun x => b.repr x i) hvH
  dsimp only at hc hw
  rw [eigenbasis_repr b C c hC,map_smul,Finsupp.smul_apply,smul_eq_mul] at hc
  rw [eigenbasis_repr b H w hH,map_smul,Finsupp.smul_apply,smul_eq_mul] at hw
  have hc' : (c i-c₀)*b.repr v i=0 := by linear_combination hc
  have hw' : (w i-w₀)*b.repr v i=0 := by linear_combination hw
  rcases hsep i with hi | hi
  · exact (mul_eq_zero.mp hc').resolve_left (sub_ne_zero.mpr hi)
  · exact (mul_eq_zero.mp hw').resolve_left (sub_ne_zero.mpr hi)

end AMSPhysical

#print axioms AMSPhysical.joint_eigenvector_zero
