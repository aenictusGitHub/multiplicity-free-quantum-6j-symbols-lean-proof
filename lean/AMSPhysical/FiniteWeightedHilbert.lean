import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical
open Module

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℝ V]

def finiteWeightedPair (w : ι → ℝ) (c : V →ₗ[ℝ] (ι → ℝ)) (p q : V) : ℝ :=
  ∑ i,w i*c p i*c q i

theorem finiteWeightedPair_symm (w : ι → ℝ) (c : V →ₗ[ℝ] (ι → ℝ)) (p q : V) :
    finiteWeightedPair w c p q=finiteWeightedPair w c q p := by
  unfold finiteWeightedPair
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem finiteWeightedPair_add_left (w : ι → ℝ) (c : V →ₗ[ℝ] (ι → ℝ)) (p q r : V) :
    finiteWeightedPair w c (p+q) r=finiteWeightedPair w c p r+finiteWeightedPair w c q r := by
  simp only [finiteWeightedPair,map_add,Pi.add_apply,mul_add,add_mul,Finset.sum_add_distrib]

theorem finiteWeightedPair_smul_left (w : ι → ℝ) (c : V →ₗ[ℝ] (ι → ℝ)) (a : ℝ) (p q : V) :
    finiteWeightedPair w c (a • p) q=a*finiteWeightedPair w c p q := by
  simp only [finiteWeightedPair,map_smul,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem finiteWeightedPair_add_right (w : ι → ℝ) (c : V →ₗ[ℝ] (ι → ℝ)) (p q r : V) :
    finiteWeightedPair w c p (q+r)=finiteWeightedPair w c p q+finiteWeightedPair w c p r := by
  simp only [finiteWeightedPair,map_add,Pi.add_apply,mul_add,Finset.sum_add_distrib]

theorem finiteWeightedPair_smul_right (w : ι → ℝ) (c : V →ₗ[ℝ] (ι → ℝ)) (a : ℝ) (p q : V) :
    finiteWeightedPair w c p (a • q)=a*finiteWeightedPair w c p q := by
  rw [finiteWeightedPair_symm,finiteWeightedPair_smul_left,finiteWeightedPair_symm w c q p]

theorem finiteWeightedPair_nonneg (w : ι → ℝ) (hw : ∀ i,0≤w i)
    (c : V →ₗ[ℝ] (ι → ℝ)) (p : V) : 0≤finiteWeightedPair w c p p := by
  apply Finset.sum_nonneg
  intro i hi
  rw [mul_assoc]
  exact mul_nonneg (hw i) (mul_self_nonneg _)

theorem finiteWeightedPair_definite (w : ι → ℝ) (hw : ∀ i,0<w i)
    (c : V →ₗ[ℝ] (ι → ℝ)) (hc : Function.Injective c) (p : V)
    (hp : finiteWeightedPair w c p p=0) : p=0 := by
  apply hc
  ext i
  rw [map_zero,Pi.zero_apply]
  have hnonneg (j : ι) (_ : j∈Finset.univ) : 0≤w j*c p j*c p j := by
    rw [mul_assoc]
    exact mul_nonneg (hw j).le (mul_self_nonneg _)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hp i (Finset.mem_univ i)
  rw [mul_assoc] at hz
  have hsq : c p i*c p i=0 := (mul_eq_zero.mp hz).resolve_left (ne_of_gt (hw i))
  exact mul_self_eq_zero.mp hsq

def finiteWeightedCore (w : ι → ℝ) (hw : ∀ i,0<w i)
    (c : V →ₗ[ℝ] (ι → ℝ)) (hc : Function.Injective c) : InnerProductSpace.Core ℝ V where
  inner := finiteWeightedPair w c
  conj_inner_symm p q := by
    change finiteWeightedPair w c q p=finiteWeightedPair w c p q
    exact finiteWeightedPair_symm w c q p
  re_inner_nonneg p := finiteWeightedPair_nonneg w (fun i => (hw i).le) c p
  add_left := finiteWeightedPair_add_left w c
  smul_left p q a := finiteWeightedPair_smul_left w c a p q
  definite := finiteWeightedPair_definite w hw c hc

def finiteWeightedNormedAddCommGroup (w : ι → ℝ) (hw : ∀ i,0<w i)
    (c : V →ₗ[ℝ] (ι → ℝ)) (hc : Function.Injective c) : NormedAddCommGroup V := by
  letI : InnerProductSpace.Core ℝ V := finiteWeightedCore w hw c hc
  exact InnerProductSpace.Core.toNormedAddCommGroup (𝕜:=ℝ)

def finiteWeightedInnerProductSpace (w : ι → ℝ) (hw : ∀ i,0<w i)
    (c : V →ₗ[ℝ] (ι → ℝ)) (hc : Function.Injective c) :
    letI := finiteWeightedNormedAddCommGroup w hw c hc
    InnerProductSpace ℝ V := by
  letI := finiteWeightedNormedAddCommGroup w hw c hc
  exact InnerProductSpace.ofCore (finiteWeightedCore w hw c hc)

def finiteWeightedBilin (w : ι → ℝ) (c : V →ₗ[ℝ] (ι → ℝ)) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (finiteWeightedPair w c)
    (finiteWeightedPair_add_left w c)
    (fun a p q => finiteWeightedPair_smul_left w c a p q)
    (finiteWeightedPair_add_right w c)
    (fun a p q => finiteWeightedPair_smul_right w c a p q)

theorem finiteWeightedPair_basis (b : Basis ι ℝ V) (w : ι → ℝ) (i j : ι) :
    finiteWeightedPair w b.equivFun.toLinearMap (b i) (b j)=if i=j then w i else 0 := by
  classical
  simp [finiteWeightedPair,Basis.equivFun_self,ite_mul,mul_ite,eq_comm]
  split_ifs with h <;> simp_all

theorem finiteWeightedAdjoint_of_basis (b : Basis ι ℝ V) (w : ι → ℝ) (A B : Module.End ℝ V)
    (h : ∀ i j,finiteWeightedPair w b.equivFun.toLinearMap (A (b i)) (b j)=
      finiteWeightedPair w b.equivFun.toLinearMap (b i) (B (b j))) (p q : V) :
    finiteWeightedPair w b.equivFun.toLinearMap (A p) q=
      finiteWeightedPair w b.equivFun.toLinearMap p (B q) := by
  have he : (finiteWeightedBilin w b.equivFun.toLinearMap).comp A=
      (finiteWeightedBilin w b.equivFun.toLinearMap).compl₂ B := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    exact h i j
  exact DFunLike.congr_fun (DFunLike.congr_fun he p) q

end AMSPhysical

#print axioms AMSPhysical.finiteWeightedCore
#print axioms AMSPhysical.finiteWeightedAdjoint_of_basis
