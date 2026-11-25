import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace AMSPhysical
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

theorem eigenspace_map_intertwiner (e : V ≃ₗ[ℝ] W) (A : Module.End ℝ V) (B : Module.End ℝ W)
    (he : ∀ v,e (A v)=B (e v)) (lam : ℝ) :
    (A.eigenspace lam).map e.toLinearMap=B.eigenspace lam := by
  ext w
  constructor
  · rintro ⟨v,hv,rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    change B (e v)=lam • e v
    rw [← he,Module.End.mem_eigenspace_iff.mp hv,map_smul]
  · intro hw
    refine ⟨e.symm w,?_,e.apply_symm_apply w⟩
    apply Module.End.mem_eigenspace_iff.mpr
    apply e.injective
    rw [he,LinearEquiv.apply_symm_apply,map_smul,LinearEquiv.apply_symm_apply]
    exact Module.End.mem_eigenspace_iff.mp hw

def eigenspaceIntertwinerEquiv (e : V ≃ₗ[ℝ] W) (A : Module.End ℝ V) (B : Module.End ℝ W)
    (he : ∀ v,e (A v)=B (e v)) (lam : ℝ) : A.eigenspace lam ≃ₗ[ℝ] B.eigenspace lam :=
  e.ofSubmodules _ _ (eigenspace_map_intertwiner e A B he lam)

theorem unit_eigenvectors_differ_by_sign (A : Module.End ℝ V) (lam : ℝ)
    (hfin : Module.finrank ℝ (A.eigenspace lam)=1) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (v w : V) (hv : A v=lam • v) (hw : A w=lam • w) (hvn : B v v=1) (hwn : B w w=1) :
    ∃ s : ℝ,(s=1 ∨ s= -1) ∧ v=s • w := by
  let x : A.eigenspace lam:=⟨w,Module.End.mem_eigenspace_iff.mpr hw⟩
  let y : A.eigenspace lam:=⟨v,Module.End.mem_eigenspace_iff.mpr hv⟩
  have hx : x≠0 := by
    intro he
    have hz : w=0 := congrArg Subtype.val he
    simp only [hz,map_zero,LinearMap.zero_apply] at hwn
    norm_num at hwn
  obtain ⟨s,hs⟩:=exists_smul_eq_of_finrank_eq_one hfin hx y
  have hvs : v=s • w := (congrArg Subtype.val hs).symm
  have hsq : s^2=1 := by
    rw [hvs] at hvn
    simpa only [map_smul,LinearMap.smul_apply,smul_eq_mul,hwn,mul_one,pow_two] using hvn
  refine ⟨s,?_,hvs⟩
  have hp : (s-1)*(s+1)=0 := by nlinarith
  rcases mul_eq_zero.mp hp with hh|hh
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

end AMSPhysical
#print axioms AMSPhysical.unit_eigenvectors_differ_by_sign
