import FiniteWeightedDuality

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
noncomputable section
namespace AMSPhysical
variable {I J V W : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- Construct the metric adjoint of an arbitrary linear map by the proved
perfect weighted dualities of its actual source and target bases. -/
def finiteWeightedAdjoint (b : Module.Basis I ℝ V) (c : Module.Basis J ℝ W)
    (w : I → ℝ) (z : J → ℝ) (hw : ∀ i,w i≠0) (T : V →ₗ[ℝ] W) : W →ₗ[ℝ] V :=
  (finiteWeightedDuality b w hw).symm.toLinearMap.comp
    (T.dualMap.comp (finiteWeightedBilin z c.equivFun.toLinearMap))

theorem finiteWeightedAdjoint_adjoint (b : Module.Basis I ℝ V) (c : Module.Basis J ℝ W)
    (w : I → ℝ) (z : J → ℝ) (hw : ∀ i,w i≠0) (T : V →ₗ[ℝ] W) (v : V) (u : W) :
    finiteWeightedBilin z c.equivFun.toLinearMap (T v) u=
      finiteWeightedBilin w b.equivFun.toLinearMap v (finiteWeightedAdjoint b c w z hw T u) := by
  have h:=congrArg (fun f : Module.Dual ℝ V => f v)
    ((finiteWeightedDuality b w hw).apply_symm_apply (T.dualMap (finiteWeightedBilin z c.equivFun.toLinearMap u)))
  change finiteWeightedPair w b.equivFun.toLinearMap (finiteWeightedAdjoint b c w z hw T u) v=
    finiteWeightedPair z c.equivFun.toLinearMap u (T v) at h
  rw [finiteWeightedPair_symm w _ _ _,finiteWeightedPair_symm z _ _ _] at h
  exact h.symm

end AMSPhysical
