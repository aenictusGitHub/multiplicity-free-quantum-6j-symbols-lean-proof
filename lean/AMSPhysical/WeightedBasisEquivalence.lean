import FiniteWeightedDuality

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace AMSPhysical
variable {I J V W : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

theorem weightedBasisEquiv_isometry (b : Module.Basis I ℝ V) (c : Module.Basis J ℝ W) (e : I ≃ J)
    (w : I → ℝ) (z : J → ℝ) (h : ∀ i,z (e i)=w i) (v u : V) :
    finiteWeightedBilin z c.equivFun.toLinearMap (b.equiv c e v) (b.equiv c e u)=
      finiteWeightedBilin w b.equivFun.toLinearMap v u := by
  have he : ((finiteWeightedBilin z c.equivFun.toLinearMap).compl₁₂ (b.equiv c e).toLinearMap
      (b.equiv c e).toLinearMap)=finiteWeightedBilin w b.equivFun.toLinearMap := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    change finiteWeightedPair z c.equivFun.toLinearMap (b.equiv c e (b i)) (b.equiv c e (b j))=
      finiteWeightedPair w b.equivFun.toLinearMap (b i) (b j)
    rw [Module.Basis.equiv_apply,Module.Basis.equiv_apply,finiteWeightedPair_basis,finiteWeightedPair_basis,h]
    simp only [e.injective.eq_iff]
  exact DFunLike.congr_fun (DFunLike.congr_fun he v) u

end AMSPhysical
