import QuantumPhysicalSnake

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
noncomputable section
namespace AMSPhysical
open scoped TensorProduct

theorem diagonalEvaluation_coevaluation {V I : Type*} [AddCommGroup V] [Module ℝ V]
    [Fintype I] [DecidableEq I] (b : Module.Basis I ℝ V) (c d : I → ℝ) :
    diagonalEvaluation b d (diagonalCoevaluation b c)=∑ i,c i*d i := by
  unfold diagonalCoevaluation
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]
  change c i*finiteWeightedPair d b.equivFun.toLinearMap (b i) (b i)=_
  rw [finiteWeightedPair_basis,if_pos rfl]

theorem inversePivotal_occupation_pairing (n L : ℕ) (x : occupationWeights (Fin (n+1)) L) :
    latticePairing (typeAInversePivotalWeight n) x.val= -((n*L:ℕ):ℤ)+2*occupationHeightZ n L x := by
  unfold occupationHeightZ latticePairing typeAInversePivotalWeight
  simp only [add_mul,Finset.sum_add_distrib,mul_assoc,← Finset.mul_sum]
  rw [x.property.2]
  push_cast
  ring

theorem occupationCompact_opposite_ratio (q : ℝ) (hq : 0<q) (n L : ℕ)
    (x : occupationWeights (Fin (n+1)) L) :
    occupationCompactWeight q n L x/occupationOppositeWeight q n L x=
      q^(latticePairing (typeAInversePivotalWeight n) x.val) := by
  apply (div_eq_iff (ne_of_gt (occupationOppositeWeight_pos q hq n L x))).mpr
  have hp : q^(latticePairing (typeAInversePivotalWeight n) x.val)*
      q^((n*L:ℕ):ℤ)*q^(occupationEnergy n L x-occupationHeightZ n L x)=
      q^(occupationEnergy n L x+occupationHeightZ n L x) := by
    rw [← zpow_add₀ (ne_of_gt hq),← zpow_add₀ (ne_of_gt hq),inversePivotal_occupation_pairing]
    congr 1
    ring
  unfold occupationCompactWeight occupationOppositeWeight
  linear_combination -(occupationFactorialProduct q n L x/qfactorial q L)*hp

/-- The reverse physical loop has the SAME proved quantum Weyl dimension,
obtained directly from the actual inverse-pivotal occupation trace. -/
theorem symmetricReverseEvaluation_loop_dimension (q : ℝ) (hq : 0<q) (n L : ℕ) :
    symmetricReverseEvaluation q n L (symmetricReverseCoevaluation q n L)=
      qfactorial q (n+L)/(qfactorial q n*qfactorial q L) := by
  change diagonalEvaluation (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L)
      (fun x =>occupationDualSign n L x*occupationCompactWeight q n L x)
      (diagonalCoevaluation (quantumOccupationBasis (K:=ℝ) (ι:=Fin (n+1)) L)
        (fun x =>occupationDualSign n L x/occupationOppositeWeight q n L x))=_
  rw [diagonalEvaluation_coevaluation]
  calc
    _ = ∑ x : occupationWeights (Fin (n+1)) L,occupationCompactWeight q n L x/occupationOppositeWeight q n L x := by
      apply Finset.sum_congr rfl
      intro x hx
      have hs:=occupationDualSign_square n L x
      calc
        _ = (occupationDualSign n L x*occupationDualSign n L x)*
            (occupationCompactWeight q n L x/occupationOppositeWeight q n L x) := by ring
        _ = _ := by rw [hs,one_mul]
    _ = ∑ x : occupationWeights (Fin (n+1)) L,q^(latticePairing (typeAInversePivotalWeight n) x.val) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact occupationCompact_opposite_ratio q hq n L x
    _ = _ := by rw [← finiteOccupationCartan_trace,inversePivotal_trace_factorial q hq]

end AMSPhysical
#print axioms AMSPhysical.symmetricReverseEvaluation_loop_dimension
