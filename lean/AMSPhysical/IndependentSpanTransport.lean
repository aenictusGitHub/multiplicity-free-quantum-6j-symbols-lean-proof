import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical
variable {I V W : Type*} [Fintype I] [DecidableEq I]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

def independentSpanTransport (b : I → V) (c : I → W)
    (hb : LinearIndependent ℝ b) (hc : LinearIndependent ℝ c) (a : I → ℝ) (ha : ∀ i,a i≠0) :
    Submodule.span ℝ (Set.range b) ≃ₗ[ℝ] Submodule.span ℝ (Set.range c) :=
  (Module.Basis.span hb).equivFun.trans
    ((LinearEquiv.piCongrRight (fun i =>LinearEquiv.smulOfNeZero (M:=ℝ) ℝ (a i) (ha i))).trans
      (Module.Basis.span hc).equivFun.symm)

theorem independentSpanTransport_basis (b : I → V) (c : I → W)
    (hb : LinearIndependent ℝ b) (hc : LinearIndependent ℝ c) (a : I → ℝ) (ha : ∀ i,a i≠0) (i : I) :
    (independentSpanTransport b c hb hc a ha
      ⟨b i,Submodule.subset_span (Set.mem_range_self i)⟩).val=a i • c i := by
  have hb0 : (⟨b i,Submodule.subset_span (Set.mem_range_self i)⟩ : Submodule.span ℝ (Set.range b))=
      Module.Basis.span hb i := Subtype.ext (Module.Basis.span_apply hb i).symm
  rw [hb0]
  have h : independentSpanTransport b c hb hc a ha (Module.Basis.span hb i)=a i • Module.Basis.span hc i := by
    apply (Module.Basis.span hc).equivFun.injective
    ext j
    simp only [independentSpanTransport,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,
      Module.Basis.equivFun_self,LinearEquiv.piCongrRight_apply,LinearEquiv.smulOfNeZero_apply,
      map_smul,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
    split_ifs with hji
    · subst j
      ring
    · ring
  exact congrArg Subtype.val h |>.trans (by simp only [Submodule.coe_smul_of_tower,Module.Basis.span_apply])

end AMSPhysical
