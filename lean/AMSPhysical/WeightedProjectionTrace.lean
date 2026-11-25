import CompactHighestPartialIsometry
import FiniteWeightedDuality

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
noncomputable section
namespace AMSPhysical
variable {V W I:Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W] [Fintype I] [DecidableEq I]
  {q:ℝ} {n:ℕ} {lam:Fin n → ℤ}

/-- Exact weighted-basis trace of an actual partial channel isometry.
The supplied eigenvalues concern an actual algebra element, not a formal
candidate dimension. -/
theorem CompactHighestRealization.channelTransfer_weighted_trace (hq:q≠0)
    (X:CompactHighestRealization q n V lam) (Y:CompactHighestRealization q n W lam)
    (b:Module.Basis I ℝ V) (w:I → ℝ) (hw:∀ i,w i≠0)
    (hB:∀ i v,X.pairing (b i) v=w i*b.repr v i)
    (z:UqTypeA q n) (e:I → ℝ) (hz:∀ i,X.action z (b i)=e i • b i) :
    (∑ i,e i/w i*Y.pairing (X.channelTransfer hq Y (b i)) (X.channelTransfer hq Y (b i)))=
      LinearMap.trace ℝ X.channel (X.channelAction z) := by
  rw [← X.channelProjection_trace z,LinearMap.trace_eq_matrix_trace ℝ b]
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro i hi
  rw [X.channelTransfer_metric_projection,hB]
  simp only [Matrix.diag_apply,LinearMap.toMatrix_apply,LinearMap.comp_apply,hz,map_smul,
    Submodule.coe_smul_of_tower,Finsupp.smul_apply,smul_eq_mul]
  field_simp [hw i]
  rfl

end AMSPhysical
#print axioms AMSPhysical.CompactHighestRealization.channelTransfer_weighted_trace
