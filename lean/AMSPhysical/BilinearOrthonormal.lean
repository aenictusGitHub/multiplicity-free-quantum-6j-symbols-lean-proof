import BilinearAdjoint
import Mathlib.LinearAlgebra.LinearIndependent.Defs

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AMSPhysical
open Module
variable {ι V : Type*} [DecidableEq ι] [AddCommGroup V] [Module ℝ V]

theorem bilinear_orthonormal_independent (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (v : ι → V)
    (h : ∀ i j,B (v i) (v j)=if i=j then 1 else 0) : LinearIndependent ℝ v := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c he i hi
  have hb := congrArg (fun p => B p (v i)) he
  simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,smul_eq_mul,
    map_zero,LinearMap.zero_apply,h,mul_ite,mul_one,mul_zero] at hb
  simpa only [Finset.sum_ite_eq',if_pos hi] using hb

theorem sigmaOrthonormal_pair {α : Type*} {β : α → Type*}
    [DecidableEq α] [∀ a,DecidableEq (β a)]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (f : ∀ a,β a → V)
    (hself : ∀ a i j,B (f a i) (f a j)=if i=j then 1 else 0)
    (hcross : ∀ a b,a≠b → ∀ i j,B (f a i) (f b j)=0)
    (p v : Sigma β) : B (f p.1 p.2) (f v.1 v.2)=if p=v then 1 else 0 := by
  classical
  rcases p with ⟨a,i⟩
  rcases v with ⟨b,j⟩
  by_cases hab : a=b
  · subst b
    rw [hself]
    congr 1
    exact propext ⟨fun h => by change i=j at h;subst j;rfl,
      fun h => eq_of_heq (Sigma.mk.inj h).2⟩
  · rw [hcross a b hab,if_neg (fun h => hab (Sigma.mk.inj h).1)]

end AMSPhysical

#print axioms AMSPhysical.bilinear_orthonormal_independent
