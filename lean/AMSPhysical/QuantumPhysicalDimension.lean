import FiniteWeightActions
import Normalization
import Mathlib.LinearAlgebra.Trace

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
noncomputable section
namespace AMSPhysical

/-- Quantum dimension is the trace of the actual pivotal K operator on the
independently constructed finite highest-weight representation. -/
def physicalQuantumDimension (q : ℝ) (L : ℕ) : ℝ :=
  LinearMap.trace ℝ (finiteWeightSpace (K:=ℝ) L) (finiteQuantumK q L)

theorem physicalQuantumDimension_eq_qnum (q : ℝ) (L : ℕ) :
    physicalQuantumDimension q L=qnum q (L+1) := by
  classical
  unfold physicalQuantumDimension
  rw [LinearMap.trace_eq_matrix_trace ℝ (standardWeightBasis (K:=ℝ) L)]
  unfold Matrix.trace
  simp only [Matrix.diag_apply,LinearMap.toMatrix_apply,standardWeightBasis_K,map_smul,
    Module.Basis.repr_self,Finsupp.smul_apply,smul_eq_mul,Finsupp.single_eq_same,mul_one]
  calc
    _ = ∑ k∈Finset.range (L+1),q^((L:ℤ)-2*(k:ℤ)) :=
      Fin.sum_univ_eq_sum_range (fun k : ℕ => q^((L:ℤ)-2*(k:ℤ))) (L+1)
    _ = qnum q (L+1) := by
      unfold qnum
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      omega

theorem physicalQuantumDimension_pos (q : ℝ) (hq : 0<q) (L : ℕ) :
    0<physicalQuantumDimension q L := by
  rw [physicalQuantumDimension_eq_qnum]
  exact qnum_pos q hq _ (by omega)

end AMSPhysical

#print axioms AMSPhysical.physicalQuantumDimension_eq_qnum
