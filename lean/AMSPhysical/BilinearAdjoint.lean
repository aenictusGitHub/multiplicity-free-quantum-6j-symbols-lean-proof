import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AMSPhysical
open Module
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def PairAdjoint (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (A A' : Module.End ℝ V) : Prop :=
  ∀ p q,B (A p) q=B p (A' q)

theorem PairAdjoint.id (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : PairAdjoint B 1 1 := fun _ _ => rfl

theorem PairAdjoint.add {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {A A' C C' : Module.End ℝ V}
    (hA : PairAdjoint B A A') (hC : PairAdjoint B C C') : PairAdjoint B (A+C) (A'+C') := by
  intro p q
  simp only [LinearMap.add_apply,map_add]
  rw [hA p q,hC p q]

theorem PairAdjoint.smul {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {A A' : Module.End ℝ V}
    (hA : PairAdjoint B A A') (a : ℝ) : PairAdjoint B (a • A) (a • A') := by
  intro p q
  simp only [LinearMap.smul_apply,map_smul,LinearMap.smul_apply,smul_eq_mul]
  rw [hA p q]

theorem PairAdjoint.mul {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {A A' C C' : Module.End ℝ V}
    (hA : PairAdjoint B A A') (hC : PairAdjoint B C C') : PairAdjoint B (A*C) (C'*A') := by
  intro p q
  change B (A (C p)) q=B p (C' (A' q))
  rw [hA,hC]

theorem PairAdjoint.symm {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
    (hB : ∀ p q,B p q=B q p) {A A' : Module.End ℝ V}
    (hA : PairAdjoint B A A') : PairAdjoint B A' A := by
  intro p q
  rw [hB (A' p) q,← hA q p,hB (A q) p]

theorem pairAdjoint_eigen_orthogonal {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
    {A : Module.End ℝ V} (hA : PairAdjoint B A A) (p q : V) (a b : ℝ)
    (hp : A p=a • p) (hq : A q=b • q) (hab : a≠b) : B p q=0 := by
  have he := hA p q
  rw [hp,hq] at he
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul] at he
  exact (mul_eq_zero.mp (by nlinarith : (a-b)*B p q=0)).resolve_left (sub_ne_zero.mpr hab)

end AMSPhysical
